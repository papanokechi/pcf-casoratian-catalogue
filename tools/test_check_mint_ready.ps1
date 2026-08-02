<#
.SYNOPSIS
  Harness for tools/check_mint_ready.ps1. Exercises every exit code the gate
  can return, on fixtures that are asserted to be distinct before the subject
  is run at all.

.DESCRIPTION
  Shipped alongside the control rather than kept elsewhere, because a test
  kept elsewhere is a test that will not be re-run.

  TWO DISCIPLINES THIS FILE EXISTS TO SATISFY.

  (1) A control that has only ever passed is indistinguishable from a control
      wired to pass. So every exit code is exercised, and the fixtures are
      asserted DISTINCT by direct observation first -- if the fixtures are
      secretly identical, six agreeing verdicts indict the harness rather
      than vindicate the subject.

  (2) This harness reports failures with an exit code. Its predecessor in the
      sibling repository printed "failures: N" and exited 0 whatever N was,
      having been committed an hour earlier as the evidence that the control
      it tested worked.

  The Zenodo-dependent cases deliberately use the LIVE API against the real
  concept record rather than a stub: "already published" is checked by
  declaring v1.0 (which is live) and "ready" by declaring v1.1 (which is not).
  A stub would agree with reality only in the environment where it was
  written.
#>
[CmdletBinding()]
param([string] $Subject = (Join-Path $PSScriptRoot "check_mint_ready.ps1"))

$ErrorActionPreference = 'Stop'
if (-not (Test-Path $Subject)) { Write-Host "CANNOT RUN: subject not found: $Subject"; exit 3 }

$concept = "20663484"
$root = Join-Path ([IO.Path]::GetTempPath()) ("mintfix_" + [Guid]::NewGuid().ToString("N").Substring(0, 12))
New-Item -ItemType Directory -Force $root | Out-Null
Write-Host "fixture root: $root"

function New-Meta([string]$dir, [string]$zver, [string]$cver) {
    Set-Content (Join-Path $dir ".zenodo.json") ('{"version": "' + $zver + '", "title": "fixture"}') -Encoding utf8
    Set-Content (Join-Path $dir "CITATION.cff") @(
        'cff-version: 1.2.0'
        'message: "fixture"'
        'title: "fixture"'
        ('version: "' + $cver + '"')
        ('doi: "10.5281/zenodo.' + $concept + '"')
    ) -Encoding utf8
}

git init -q --bare "$root\origin.git" -b main 2>$null

function New-Fixture([string]$name, [string]$zver, [string]$cver) {
    # Each fixture gets its OWN bare origin. A shared one would make every
    # fixture's push advance the same ref, so the first fixture would end up
    # legitimately behind the server and the "ready" case would report
    # UNPUSHED -- a fixture fault presenting as a subject failure.
    $p = "$root\$name"
    $o = "$root\$name.git"
    git init -q --bare $o -b main *> $null
    git clone -q $o $p *> $null
    git -C $p config user.email "harness@local" *> $null
    git -C $p config user.name  "harness"       *> $null
    git -C $p checkout -q -B main *> $null
    New-Meta $p $zver $cver
    # A per-fixture file, so the commit is never empty. Without it a fixture
    # whose metadata matched an earlier one produced NOTHING TO COMMIT, which
    # git prints to stdout -- and stdout inside a function is return value.
    Set-Content (Join-Path $p "FIXTURE.txt") "fixture: $name" -Encoding utf8
    git -C $p add -A *> $null
    git -C $p commit -q -m "fixture $name" *> $null
    git -C $p push -q origin main *> $null
    $p
}

$ready     = New-Fixture "ready"     "1.1" "1.1"
$dirty     = New-Fixture "dirty"     "1.1" "1.1"
$unpushed  = New-Fixture "unpushed"  "1.1" "1.1"
$conflict  = New-Fixture "conflict"  "1.1" "1.1"
$published = New-Fixture "published" "1.0" "1.0"
Set-Content "$dirty\stray.txt" "uncommitted" -Encoding utf8
Set-Content "$unpushed\extra.txt" "committed but not pushed" -Encoding utf8
git -C $unpushed add -A *> $null; git -C $unpushed commit -q -m "not pushed" *> $null
New-Meta $conflict "1.1" "1.2"
git -C $conflict add -A *> $null
git -C $conflict commit -q -m "conflicting versions" *> $null
git -C $conflict push -q origin main *> $null
$norepo = "$root\norepo"; New-Item -ItemType Directory -Force $norepo | Out-Null

Write-Host ""
Write-Host "--- fixture assertion (direct observation, not the subject's report) ---"
foreach ($n in @("ready", "dirty", "unpushed", "conflict", "published")) {
    $p = "$root\$n"
    $zv = (Get-Content "$p\.zenodo.json" -Raw | ConvertFrom-Json).version
    $cv = ((Get-Content "$p\CITATION.cff" | Where-Object { $_ -match '^version:' }) -replace '^version:\s*"?([^"]+)"?.*', '$1')
    $d  = @(git -C $p status --porcelain).Count
    $h  = (git -C $p rev-parse HEAD).Substring(0, 7)
    $r  = ((git -C $p ls-remote origin refs/heads/main) -split "`t")[0]
    $r  = if ($r) { $r.Substring(0, 7) } else { "(none)" }
    "  {0,-10} zenodo={1,-4} cff={2,-4} dirty={3}  head={4} server={5} {6}" -f `
        $n, $zv, $cv, $d, $h, $r, $(if ($h -eq $r) { "in-sync" } else { "DIVERGED" })
}
"  {0,-10} no .git present" -f "norepo"
Write-Host "  fixtures differ in exactly one axis each: version-vs-live, dirtiness, push state, metadata agreement."
Write-Host "  (a uniform verdict across these would indict this harness, not the subject)"

Write-Host ""
Write-Host "--- subject under test ---"
$cases = @(
    @{ n = "ready (v1.1 unminted, clean, pushed)"; p = $ready;     api = $null; want = 0 }
    @{ n = "dirty tree";                           p = $dirty;     api = $null; want = 1 }
    @{ n = "committed but not on server";          p = $unpushed;  api = $null; want = 2 }
    @{ n = "not a git repository";                 p = $norepo;    api = $null; want = 3 }
    @{ n = "Zenodo unreachable";                   p = $ready;     api = "http://127.0.0.1:9/api/records"; want = 3 }
    @{ n = "v1.0 is already published";            p = $published; api = $null; want = 4 }
    @{ n = "metadata versions disagree";           p = $conflict;  api = $null; want = 5 }
)

$failures = 0
$seen = @()
foreach ($c in $cases) {
    $args = @("-NoProfile", "-File", $Subject, "-RepoPath", $c.p, "-TimeoutSec", "8")
    if ($c.api) { $args += @("-ZenodoApi", $c.api) }
    & pwsh @args *> $null
    $got = $LASTEXITCODE
    $seen += $got
    $ok = ($got -eq $c.want)
    if (-not $ok) { $failures++ }
    "  {0,-38} expect {1}  got {2}  {3}" -f $c.n, $c.want, $got, $(if ($ok) { "OK" } else { "FAIL" })
}

Write-Host ""
Write-Host ("distinct expected codes exercised: " + (($cases.want | Sort-Object -Unique) -join ","))
Write-Host ("observed codes in order          : " + ($seen -join ","))
Write-Host "failures: $failures (expect 0)"

Remove-Item -Recurse -Force $root -ErrorAction SilentlyContinue
Write-Host "fixtures removed."

# The exit code is the point. Printing the count and exiting 0 regardless is
# the defect this line exists to not have.
if ($failures -gt 0) { exit 1 }
exit 0
