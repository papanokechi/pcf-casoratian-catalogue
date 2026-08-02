<#
.SYNOPSIS
  Verify that verify/*.lean are byte-faithful mirrors of the pcf-delta host sources.

.DESCRIPTION
  This repository's published Zenodo metadata (concept 10.5281/zenodo.20663484) states that
  pcf-delta "hosts and builds the Lean core" and that the files in verify/ are "byte-faithful
  mirrors of the pcf-delta host sources". That is a binding claim on a minted, immutable record.

  Until this script existed the claim was held by convention alone: nothing compared the two
  repositories, so drift would raise no error in either tree, break no build, and appear in no
  diff a reader would encounter. A requirement asserted in prose and never instantiated is a
  control whose "cannot run" state occupies its entire space.

  Two design points are deliberate.

  1. It compares GIT BLOB SHAs, not worktree bytes. Worktree bytes can agree by the coincidence
     of two repositories sharing core.autocrlf, and disagree on another machine or a fresh
     clone. The blob is what git records and what the deposit carries, so the blob is the thing
     the claim is actually about.

  2. "Cannot run" is a distinct terminal state (exit 3), never folded into success. If the host
     repository is missing, is not a git repository, or does not carry one of these files, this
     script must not report a verified mirror. An unreachable oracle is not evidence of
     agreement -- the same rule the deposit script applies to an unreachable Zenodo.

.PARAMETER HostRepo
  Path to the pcf-delta working copy. Falls back to $env:PCF_DELTA_ROOT, then to sibling
  and known-layout guesses.

.PARAMETER Quiet
  Print only the verdict line.

.OUTPUTS
  Exit 0  every mirrored file matches the host, and both trees are clean for those paths
  Exit 1  DRIFT -- a mirrored blob differs from its host blob
  Exit 2  a tree has uncommitted changes to these paths; the comparison of committed blobs
          still held, but the working copy has moved away from what was compared
  Exit 3  CANNOT RUN -- host repo, git, or a host file was unavailable. Not a pass.
#>
[CmdletBinding()]
param(
    [string] $HostRepo,
    [switch] $Quiet
)

Set-StrictMode -Version Latest

$MirrorRepo = Split-Path -Parent $PSScriptRoot

# name -> path within the host repo. The mirror path is always verify/<name>.
$Mirrored = [ordered]@{
    'GeneralCaso.lean' = 'lean/pcf_continuant/PcfContinuant/GeneralCaso.lean'
    'HigherCaso.lean'  = 'lean/pcf_continuant/PcfContinuant/HigherCaso.lean'
    'HermitePade.lean' = 'lean/pcf_continuant/PcfContinuant/HermitePade.lean'
}

function Write-Line { param([string] $Text) if (-not $Quiet) { Write-Host $Text } }

function Exit-CannotRun {
    param([string] $Reason)
    [Console]::Error.WriteLine("CANNOT VERIFY MIRROR - $Reason")
    [Console]::Error.WriteLine("  This is exit 3, not a pass. The byte-faithfulness claim on")
    [Console]::Error.WriteLine("  10.5281/zenodo.20663484 is unverified, not confirmed.")
    [Console]::Error.WriteLine("  If the host path is right, check which branch it is on: a second")
    [Console]::Error.WriteLine("  working copy of pcf-delta can lack these files entirely at HEAD.")
    exit 3
}

if (-not (Get-Command git -ErrorAction SilentlyContinue)) {
    Exit-CannotRun "git is not on PATH"
}

if (-not $HostRepo) {
    $candidates = @()
    if ($env:PCF_DELTA_ROOT) { $candidates += $env:PCF_DELTA_ROOT }
    $candidates += (Join-Path (Split-Path -Parent $MirrorRepo) 'pcf-delta')
    $candidates += 'C:\LocalWork\pcf-delta'
    $HostRepo = $candidates | Where-Object { $_ -and (Test-Path (Join-Path $_ '.git')) } | Select-Object -First 1
}

if (-not $HostRepo) {
    Exit-CannotRun "pcf-delta working copy not found (set PCF_DELTA_ROOT or pass -HostRepo)"
}
if (-not (Test-Path (Join-Path $HostRepo '.git'))) {
    Exit-CannotRun "'$HostRepo' is not a git repository"
}

Write-Line "mirror : $MirrorRepo"
function Get-RepoRef {
    <#
      Branch and commit a repository is currently on. This is printed with every verdict because
      "HEAD" is a load-bearing environmental fact that the comparison depends on and does not
      otherwise state: a second working copy of the host on a different branch can hold entirely
      different content at the same paths, and a verdict that does not name the ref it read is
      a verdict a reader cannot reproduce.
    #>
    param([string] $Repo)
    $branch = & git -C $Repo rev-parse --abbrev-ref HEAD 2>$null
    $commit = & git -C $Repo rev-parse --short HEAD 2>$null
    if (-not $commit) { return '(no commits)' }
    return "$branch @ $commit"
}

Write-Line "host   : $HostRepo"
Write-Line "         $(Get-RepoRef $HostRepo)"
Write-Line "         mirror is $(Get-RepoRef $MirrorRepo)"
Write-Line ""

function Get-BlobSha {
    <#
      Blob SHA recorded at HEAD for a path, or $null when the path is absent from that tree.
      $null is always propagated as cannot-run by the caller; it is never treated as a mismatch,
      because "the host does not have this file" and "the host has a different file" are
      different facts and only one of them is drift.
    #>
    param([string] $Repo, [string] $RelPath)
    $line = & git -C $Repo ls-tree HEAD -- $RelPath 2>$null
    if ($LASTEXITCODE -ne 0 -or -not $line) { return $null }
    $meta = ($line -split "`t")[0] -split '\s+'
    if ($meta.Count -lt 3) { return $null }
    return $meta[2]
}

function Test-PathDirty {
    param([string] $Repo, [string[]] $RelPaths)
    $out = & git -C $Repo status --porcelain -- $RelPaths 2>$null
    if ($LASTEXITCODE -ne 0) { return $null }
    return @($out | Where-Object { $_ }).Count -gt 0
}

$drift = 0
$rows  = @()

foreach ($name in $Mirrored.Keys) {
    $hostRel   = $Mirrored[$name]
    $mirrorRel = "verify/$name"

    $hostSha   = Get-BlobSha -Repo $HostRepo   -RelPath $hostRel
    $mirrorSha = Get-BlobSha -Repo $MirrorRepo -RelPath $mirrorRel

    if (-not $hostSha)   { Exit-CannotRun "host has no '$hostRel' at HEAD" }
    if (-not $mirrorSha) { Exit-CannotRun "mirror has no '$mirrorRel' at HEAD" }

    $match = ($hostSha -eq $mirrorSha)
    if (-not $match) { $drift++ }

    $rows += [pscustomobject]@{
        File   = $name
        HostSha   = $hostSha.Substring(0, 12)
        MirrorSha = $mirrorSha.Substring(0, 12)
        Result = $(if ($match) { 'MATCH' } else { 'DRIFT' })
    }
}

foreach ($r in $rows) {
    Write-Line ("  {0,-18} host {1}  mirror {2}  {3}" -f $r.File, $r.HostSha, $r.MirrorSha, $r.Result)
}
Write-Line ""

if ($drift -gt 0) {
    [Console]::Error.WriteLine("MIRROR DRIFT - $drift of $($rows.Count) file(s) differ from the host.")
    [Console]::Error.WriteLine("  10.5281/zenodo.20663484 states these are byte-faithful mirrors of pcf-delta.")
    [Console]::Error.WriteLine("  That record is minted and cannot be corrected. Re-sync from the host before")
    [Console]::Error.WriteLine("  depositing; do not reconcile by editing the mirror to taste.")
    exit 1
}

$hostDirty   = Test-PathDirty -Repo $HostRepo   -RelPaths ([string[]]$Mirrored.Values)
$mirrorDirty = Test-PathDirty -Repo $MirrorRepo -RelPaths ([string[]]($Mirrored.Keys | ForEach-Object { "verify/$_" }))

if ($null -eq $hostDirty -or $null -eq $mirrorDirty) {
    Exit-CannotRun "could not read working-tree status for the mirrored paths"
}

$stamp = (Get-Date).ToString('yyyy-MM-dd')

if ($hostDirty -or $mirrorDirty) {
    $which = @()
    if ($hostDirty)   { $which += 'HOST' }
    if ($mirrorDirty) { $which += 'MIRROR' }
    [Console]::Error.WriteLine("COMMITTED BLOBS MATCH, BUT THE $($which -join ' AND ') WORKING TREE HAS MOVED.")
    [Console]::Error.WriteLine("  The comparison above is of committed blobs and it held. It says nothing about")
    [Console]::Error.WriteLine("  the uncommitted edits now sitting on these paths. Commit or discard, re-run.")
    exit 2
}

Write-Line "MIRROR VERIFIED $stamp - $($rows.Count) file(s), committed blobs identical, both trees clean."
Write-Line "  Evidence is the blob SHAs above; they are checkable against both repositories"
Write-Line "  rather than taken on this script's word."
exit 0
