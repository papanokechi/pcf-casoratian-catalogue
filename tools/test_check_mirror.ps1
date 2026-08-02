# Harness for tools/check_mirror.ps1.
# Class-11 discipline: the fixtures live in $env:TEMP under distinctive names, share no
# variable or directory namespace with the subject, and each fixture's DIFFERENCE is asserted
# by direct observation before any of the subject's output is read.

$ErrorActionPreference = 'Stop'

$subject  = Join-Path $PSScriptRoot 'check_mirror.ps1'
$realMirr = Join-Path (Split-Path -Parent $PSScriptRoot) 'verify'
$fixRoot  = Join-Path $env:TEMP ('mirrorfix_' + (Get-Random))
$gitId    = @('-c','user.email=fixture@local','-c','user.name=fixture')
$leanRel  = 'lean/pcf_continuant/PcfContinuant'

function New-FixtureHost {
    param([string] $Tag, [scriptblock] $Mutate)
    $root = Join-Path $fixRoot $Tag
    $dir  = Join-Path $root $leanRel.Replace('/','\')
    New-Item -ItemType Directory -Force $dir | Out-Null
    foreach ($nm in 'GeneralCaso.lean','HigherCaso.lean','HermitePade.lean') {
        Copy-Item (Join-Path $realMirr $nm) (Join-Path $dir $nm)
    }
    & git init -q $root 2>&1 | Out-Null
    if ($Mutate) { & $Mutate $dir }
    & git @gitId -C $root add -A 2>&1 | Out-Null
    & git @gitId -C $root commit -q -m "fixture $Tag" 2>&1 | Out-Null
    return $root
}

function Get-HeadBlob {
    param([string] $Repo, [string] $RelPath)
    $ln = & git -C $Repo ls-tree HEAD -- $RelPath 2>$null
    if (-not $ln) { return '(absent)' }
    return (($ln -split "`t")[0] -split '\s+')[2].Substring(0,12)
}

Write-Host "fixture root: $fixRoot`n"

# --- build fixtures -------------------------------------------------------------------
$hostClean = New-FixtureHost 'clean'  $null
$hostDrift = New-FixtureHost 'drift'  { param($d) Add-Content (Join-Path $d 'GeneralCaso.lean') "-- drift injected by fixture" }
$hostDirty = New-FixtureHost 'dirty'  $null
Add-Content (Join-Path $hostDirty "$($leanRel.Replace('/','\'))\HigherCaso.lean") "-- post-commit worktree edit"

$hostEmpty = Join-Path $fixRoot 'empty'
New-Item -ItemType Directory -Force $hostEmpty | Out-Null
& git init -q $hostEmpty 2>&1 | Out-Null
Set-Content (Join-Path $hostEmpty 'readme.txt') 'no lean here'
& git @gitId -C $hostEmpty add -A 2>&1 | Out-Null
& git @gitId -C $hostEmpty commit -q -m 'fixture empty' 2>&1 | Out-Null

$hostGone = Join-Path $fixRoot 'does-not-exist'

# --- FIXTURE ASSERTION: prove the states differ, before reading any subject output -----
Write-Host "--- fixture assertion (direct observation, not the subject's report) ---"
$mirrBlob = @{}
foreach ($nm in 'GeneralCaso.lean','HigherCaso.lean','HermitePade.lean') {
    $mirrBlob[$nm] = Get-HeadBlob (Split-Path -Parent $PSScriptRoot) "verify/$nm"
}
$distinct = @()
foreach ($nm in 'GeneralCaso.lean','HigherCaso.lean','HermitePade.lean') {
    $c = Get-HeadBlob $hostClean "$leanRel/$nm"
    $d = Get-HeadBlob $hostDrift "$leanRel/$nm"
    Write-Host ("  {0,-18} mirror {1}  clean-fx {2}  drift-fx {3}" -f $nm, $mirrBlob[$nm], $c, $d)
    $distinct += "$nm|$c|$d"
}
$gcClean = Get-HeadBlob $hostClean "$leanRel/GeneralCaso.lean"
$gcDrift = Get-HeadBlob $hostDrift "$leanRel/GeneralCaso.lean"
$hcClean = Get-HeadBlob $hostClean "$leanRel/HigherCaso.lean"
$hcDrift = Get-HeadBlob $hostDrift "$leanRel/HigherCaso.lean"

if ($gcClean -eq $gcDrift) { throw "FIXTURE INVALID: drift host has the same GeneralCaso blob as clean host - nothing was injected" }
if ($hcClean -ne $hcDrift) { throw "FIXTURE INVALID: HigherCaso differs too - the injection was not surgical, so a uniform DRIFT verdict would prove nothing" }
if ($gcClean -ne $mirrBlob['GeneralCaso.lean']) { throw "FIXTURE INVALID: clean host does not match the real mirror" }
$dirtyStatus = & git -C $hostDirty status --porcelain
if (-not $dirtyStatus) { throw "FIXTURE INVALID: dirty host reports a clean worktree" }
Write-Host "  fixtures are distinct: drift host differs on GeneralCaso ONLY; dirty host worktree is dirty."
Write-Host "  (a uniform verdict across these would indict the harness, not the subject)`n"

# --- exercise the subject -------------------------------------------------------------
$cases = @(
    @{ Tag='real repos (no -HostRepo)'; Args=@();                    Expect=0 },
    @{ Tag='clean fixture host';        Args=@('-HostRepo',$hostClean); Expect=0 },
    @{ Tag='drift fixture host';        Args=@('-HostRepo',$hostDrift); Expect=1 },
    @{ Tag='dirty fixture host';        Args=@('-HostRepo',$hostDirty); Expect=2 },
    @{ Tag='host lacks the files';      Args=@('-HostRepo',$hostEmpty); Expect=3 },
    @{ Tag='host path absent';          Args=@('-HostRepo',$hostGone);  Expect=3 }
)

Write-Host "--- subject under test ---"
$fails = 0
foreach ($case in $cases) {
    $null = & pwsh -NoProfile -File $subject @($case.Args) -Quiet 2>&1
    $got  = $LASTEXITCODE
    $ok   = ($got -eq $case.Expect)
    if (-not $ok) { $fails++ }
    Write-Host ("  {0,-26} expect {1}  got {2}  {3}" -f $case.Tag, $case.Expect, $got, $(if($ok){'OK'}else{'** FAIL **'}))
}

Write-Host ""
$codes = ($cases | ForEach-Object { $_.Expect }) -join ','
Write-Host "distinct expected codes exercised: $codes"
Write-Host "failures: $fails (expect 0)"

Remove-Item -Recurse -Force $fixRoot -ErrorAction SilentlyContinue
Write-Host "fixtures removed."

# A harness that prints its result and exits 0 regardless is the defect it exists to catch:
# wired into anything automated it passes silently. The count is the exit code.
if ($fails -gt 0) {
    [Console]::Error.WriteLine("HARNESS FAILED - $fails of $($cases.Count) case(s) returned the wrong exit code.")
    exit 1
}
exit 0
