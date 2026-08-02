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
  concept record rather than a stub: a stub would agree with reality only in
  the environment where it was written.

  BUT a live fixture may only rest on a MONOTONE fact. "v1.0 is published" is
  monotone: Zenodo records are permanent, so once true it is true forever.
  "v1.1 is not published" is NOT monotone -- and it was destroyed on
  2026-08-02 by the very mint this gate cleared. Every non-published fixture
  then returned 4 (the top severity, which masks the axis each one isolates)
  and the harness reported 5 failures against a healthy subject. The harness
  was right the day it was written and became wrong when the world moved,
  with nothing observing the transition.

  So the unpublished cases declare version 99.99, which no release will ever
  carry. The rule this encodes: a fixture asserting the ABSENCE of a public
  record is asserting something the project's own success will falsify.
#>
[CmdletBinding()]
param([string] $Subject = (Join-Path $PSScriptRoot "check_mint_ready.ps1"))

$ErrorActionPreference = 'Stop'
if (-not (Test-Path $Subject)) { Write-Host "CANNOT RUN: subject not found: $Subject"; exit 3 }

$concept = "20663484"
$root = Join-Path ([IO.Path]::GetTempPath()) ("mintfix_" + [Guid]::NewGuid().ToString("N").Substring(0, 12))
New-Item -ItemType Directory -Force $root | Out-Null
Write-Host "fixture root: $root"

function New-Meta([string]$dir, [string]$zver, [string]$cver, [string]$desc = "fixture description, tense-neutral") {
    $obj = [ordered]@{ version = $zver; title = "fixture"; description = $desc }
    Set-Content (Join-Path $dir ".zenodo.json") ($obj | ConvertTo-Json -Compress) -Encoding utf8
    Set-Content (Join-Path $dir "CITATION.cff") @(
        'cff-version: 1.2.0'
        'message: "fixture"'
        'title: "fixture"'
        ('version: "' + $cver + '"')
        ('doi: "10.5281/zenodo.' + $concept + '"')
    ) -Encoding utf8
}

git init -q --bare "$root\origin.git" -b main 2>$null

function New-Fixture([string]$name, [string]$zver, [string]$cver, [string]$desc = "fixture description, tense-neutral") {
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
    New-Meta $p $zver $cver $desc
    # A per-fixture file, so the commit is never empty. Without it a fixture
    # whose metadata matched an earlier one produced NOTHING TO COMMIT, which
    # git prints to stdout -- and stdout inside a function is return value.
    Set-Content (Join-Path $p "FIXTURE.txt") "fixture: $name" -Encoding utf8
    git -C $p add -A *> $null
    git -C $p commit -q -m "fixture $name" *> $null
    # Tag matching the declared version, so every pre-existing case isolates the
    # axis it is for. Without this each one would also trip NO VERSION TAG and
    # the codes would collapse onto 6 -- the fixture holding two variables at
    # once, which is what the assertion block below exists to catch.
    if ($zver) { git -C $p tag "v$zver" *> $null }
    git -C $p push -q origin main *> $null
    $p
}

# $UNMINTED is a version no release will ever carry, so these fixtures rest on
# a fact the world cannot revoke. See the header note: they previously declared
# 1.1, and the 2026-08-02 mint turned all five into ALREADY PUBLISHED.
$UNMINTED = "99.99"
$ready     = New-Fixture "ready"     $UNMINTED $UNMINTED
$dirty     = New-Fixture "dirty"     $UNMINTED $UNMINTED
$unpushed  = New-Fixture "unpushed"  $UNMINTED $UNMINTED
$conflict  = New-Fixture "conflict"  $UNMINTED $UNMINTED
$published = New-Fixture "published" "1.0" "1.0"
$untagged  = New-Fixture "untagged"  $UNMINTED $UNMINTED
# The description is v1.1's real shipped wording. This fixture is a regression
# test against an actual uncorrectable defect, not an invented one: both prior
# deposits permanently assert they were never made.
$selfneg   = New-Fixture "selfneg"   $UNMINTED $UNMINTED "VERSION 99.99 (DRAFT -- NOT YET MINTED, awaiting operator git-commit + Zenodo 'New version')"  # SELFNEG-OK
git -C $untagged tag -d "v$UNMINTED" *> $null
Set-Content "$dirty\stray.txt" "uncommitted" -Encoding utf8
Set-Content "$unpushed\extra.txt" "committed but not pushed" -Encoding utf8
git -C $unpushed add -A *> $null; git -C $unpushed commit -q -m "not pushed" *> $null
git -C $unpushed tag -f "v$UNMINTED" *> $null
New-Meta $conflict $UNMINTED "99.98"
git -C $conflict add -A *> $null
git -C $conflict commit -q -m "conflicting versions" *> $null
git -C $conflict tag -f "v$UNMINTED" *> $null
git -C $conflict push -q origin main *> $null
$norepo = "$root\norepo"; New-Item -ItemType Directory -Force $norepo | Out-Null

# Self-negating text AND no concept DOI. Retrodicting the gate against tag
# v0.1.3 - which has no top-level 'doi:' because the concept DOI did not exist
# yet - showed it aborting on the missing DOI and never reaching the local
# scan. So the one defect it could have caught with no network at all was the
# one it stayed silent about. Severity puts CANNOT RUN above SELF-NEGATING, so
# the exit code cannot express this: the finding must be asserted in output.
$nodoi = New-Fixture "nodoi" $UNMINTED $UNMINTED "VERSION 99.99 -- NOT YET MINTED, awaiting operator sign-off"  # SELFNEG-OK
$cffNoDoi = @(Get-Content "$nodoi\CITATION.cff") | Where-Object { $_ -notmatch '^doi:' }
Set-Content "$nodoi\CITATION.cff" $cffNoDoi -Encoding utf8
git -C $nodoi add -A *> $null
git -C $nodoi commit -q -m "no concept doi" *> $null
git -C $nodoi tag -f "v$UNMINTED" *> $null
git -C $nodoi push -q origin main *> $null

# The published pcf-delta v1.4 archive (10.5281/zenodo.20633165, md5 fc172e44...)
# carries its claim SPLIT ACROSS A LINE BREAK, with the YAML comment marker of the
# continuation line sitting between the two words, and its CITATION.cff carries a
# third casing, "NOT YET deposited". The literal list scores zero on both forms.   SELFNEG-OK
# This fixture is that text; the only edit is the version number. A fixture the
# subject's author invented would share the author's blind spot, which is the
# whole reason the previous list missed a real deposit for two months.
$prefail = 0
$splitclaim = New-Fixture "splitclaim" $UNMINTED $UNMINTED
Add-Content "$splitclaim\METADATA.yml" @(
    'zenodo:'
    ('  # v' + $UNMINTED + ' (current LIVE draft; sigma_3 promoted) is NOT YET')   # SELFNEG-OK
    '  # DEPOSITED - its version DOI is minted by hand at deposit time.'           # SELFNEG-OK
    '  date_released: "2026-06-10"  # DRAFT prepared for sharing; NOT YET deposited.'  # SELFNEG-OK
) -Encoding utf8
git -C $splitclaim add -A *> $null
git -C $splitclaim commit -q -m "self-negating claim split across lines" *> $null
git -C $splitclaim tag -f "v$UNMINTED" *> $null
git -C $splitclaim push -q origin main *> $null

Write-Host ""
Write-Host "--- fixture assertion (direct observation, not the subject's report) ---"
foreach ($n in @("ready", "dirty", "unpushed", "conflict", "published", "untagged")) {
    $p = "$root\$n"
    $zv = (Get-Content "$p\.zenodo.json" -Raw | ConvertFrom-Json).version
    $cv = ((Get-Content "$p\CITATION.cff" | Where-Object { $_ -match '^version:' }) -replace '^version:\s*"?([^"]+)"?.*', '$1')
    $d  = @(git -C $p status --porcelain).Count
    $h  = (git -C $p rev-parse HEAD).Substring(0, 7)
    $r  = ((git -C $p ls-remote origin refs/heads/main) -split "`t")[0]
    $r  = if ($r) { $r.Substring(0, 7) } else { "(none)" }
    $tg = @(git -C $p tag --points-at HEAD 2>$null | Where-Object { $_ })
    $tg = if ($tg.Count) { $tg -join "," } else { "(untagged)" }
    "  {0,-10} zenodo={1,-4} cff={2,-4} dirty={3}  head={4} server={5} tag={6,-10} {7}" -f `
        $n, $zv, $cv, $d, $h, $r, $tg, $(if ($h -eq $r) { "in-sync" } else { "DIVERGED" })
}
"  {0,-10} no .git present" -f "norepo"

# Direct observation that this fixture exercises the SPLIT pass and not the literal
# one. Without it, a fixture that happened to carry a contiguous phrase would exit 7
# for the old reason and report the new pass as working - the same shape as the
# inversion regex that matched nothing and was read as proof a harness could not fail.
$litPhrases = @('NOT YET MINTED', 'NOT YET DEPOSITED', 'not yet minted',            # SELFNEG-OK
                'not yet deposited', 'awaiting operator', 'will only exist after',  # SELFNEG-OK
                'not been deposited', 'to be minted', 'NOT YET PUBLISHED',          # SELFNEG-OK
                'not yet published')                                                # SELFNEG-OK
$sm = @(Get-Content "$splitclaim\METADATA.yml")
$litHits = 0
foreach ($ln in $sm) { foreach ($ph in $litPhrases) { if ($ln.Contains($ph)) { $litHits++ } } }
$hasSplit = (($sm -join "`n") -match '(?i)NOT\s+YET\s*\r?\n\s*#\s*DEPOSITED')       # SELFNEG-OK
"  {0,-10} literal-list hits={1} (must be 0)  claim split across lines={2} (must be True)" -f "splitclaim", $litHits, $hasSplit
if ($litHits -ne 0 -or -not $hasSplit) {
    Write-Host "  FIXTURE FAULT: splitclaim does not exercise the split-claim pass; a pass here would mean nothing"
    $prefail++
}
Write-Host "  fixtures differ in exactly one axis each: version-vs-live, dirtiness, push state, metadata agreement, tagging."
Write-Host "  (a uniform verdict across these would indict this harness, not the subject)"

Write-Host ""
Write-Host "--- subject under test ---"
$cases = @(
    @{ n = "ready (unminted version, clean, pushed)"; p = $ready;   api = $null; want = 0 }
    @{ n = "dirty tree";                           p = $dirty;     api = $null; want = 1 }
    @{ n = "committed but not on server";          p = $unpushed;  api = $null; want = 2 }
    @{ n = "not a git repository";                 p = $norepo;    api = $null; want = 3 }
    @{ n = "Zenodo unreachable";                   p = $ready;     api = "http://127.0.0.1:9/api/records"; want = 3 }
    @{ n = "v1.0 is already published";            p = $published; api = $null; want = 4 }
    @{ n = "metadata versions disagree";           p = $conflict;  api = $null; want = 5 }
    @{ n = "HEAD carries no version tag";          p = $untagged;  api = $null; want = 6 }
    @{ n = "metadata says it is not yet minted";   p = $selfneg;   api = $null; want = 7 }   # SELFNEG-OK
    @{ n = "claim split across lines by a comment"; p = $splitclaim; api = $null; want = 7
       must = @("across a line break or comment marker") }
    @{ n = "no concept DOI: local checks still run"; p = $nodoi;   api = $null; want = 3
       must = @("SELF-NEGATING", "the already-published check cannot run") }
)

$failures = $prefail
$seen = @()
foreach ($c in $cases) {
    $args = @("-NoProfile", "-File", $Subject, "-RepoPath", $c.p, "-TimeoutSec", "8")
    if ($c.api) { $args += @("-ZenodoApi", $c.api) }
    $out = (& pwsh @args 2>&1 | Out-String)
    $got = $LASTEXITCODE
    $seen += $got
    $ok = ($got -eq $c.want)
    # Exit code alone cannot express "this check still ran even though a
    # different one could not". The severity order means a CANNOT RUN masks a
    # lower-ranked finding in the code, so the finding has to be asserted in the
    # output or the regression is invisible.
    $noteMsg = ""
    if ($c.must) {
        foreach ($m in @($c.must)) {
            if ($out -notmatch [regex]::Escape($m)) { $ok = $false; $noteMsg = " [missing: $m]" }
        }
    }
    if ($c.mustNot) {
        foreach ($m in @($c.mustNot)) {
            if ($out -match [regex]::Escape($m)) { $ok = $false; $noteMsg = " [unexpected: $m]" }
        }
    }
    if (-not $ok) { $failures++ }
    "  {0,-38} expect {1}  got {2}  {3}{4}" -f $c.n, $c.want, $got, $(if ($ok) { "OK" } else { "FAIL" }), $noteMsg
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
