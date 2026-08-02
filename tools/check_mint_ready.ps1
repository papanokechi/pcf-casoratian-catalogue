<#
.SYNOPSIS
  Mint gate: refuses to report a repository ready for a Zenodo "New version"
  while the version it declares is already published, while its tree is
  uncommitted, while its commits are not on the server, or while it cannot
  find out.

.DESCRIPTION
  A Zenodo record cannot be withdrawn. Every failure this gate reports is
  cheap; the failure it exists to prevent is permanent.

  WHY THIS FILE EXISTS, AND WHY IT IS HERE RATHER THAN ONLY IN pcf-delta.
  On 2026-08-02 the companion repository pcf-delta had accumulated four
  deposit guards -- assembly, a clean/pushed gate, metadata validation, and a
  mint guard that asks Zenodo whether the version is already live. Each was
  written at the site of the failure that motivated it. None was written to
  the shape "a repository that mints Zenodo deposits". This repository is
  exactly that shape, was about to mint v1.1, and had none of them.

  A fix applied where the last failure happened is not a fix applied to what
  failed.

  DELIBERATE DIFFERENCE FROM pcf-delta's GATE. That gate establishes "pushed"
  by counting origin/<branch>..HEAD, which reads refs/remotes/origin/* -- a
  LOCAL CACHE of the server, refreshed only by fetch. Its answer is therefore
  correct only in an environment where a fetch has just run, and it states an
  affirmation ("committed and on origin/<branch>") that licenses an
  irreversible act. This gate asks the server directly with `git ls-remote`
  and treats an unreachable remote as CANNOT RUN, never as "pushed".

  EVERY CHECK RUNS, ALWAYS. The gate does not stop at the first failure,
  because an operator who fixes only what was reported and re-runs is an
  operator who discovers the terminal condition last. All findings print; the
  exit code is the most severe.

  Exit codes:
    0  READY             - declared version is unminted, tree clean, on the server, tagged
    1  DIRTY             - some tracked path is uncommitted, staged or untracked
    2  UNPUSHED          - HEAD is not the commit the server has for this branch
    3  CANNOT RUN        - not a git repo, no metadata, no branch, or Zenodo/remote unreachable
    4  ALREADY PUBLISHED - the declared version is live; minting would duplicate it, permanently
    5  VERSION CONFLICT  - .zenodo.json and CITATION.cff declare different versions
    6  NO VERSION TAG    - HEAD carries no tag matching the declared version, so the
                           uploaded archive would name no point in history
    7  SELF-NEGATING     - the metadata about to be deposited asserts that it has not
                           been deposited. Both prior deposits shipped this: v1.0's
                           archive says "NOT YET DEPOSITED", v1.1's says "NOT YET    SELFNEG-OK
                           MINTED". Neither can be corrected. The text is written
                           before the mint and the mint falsifies it, so pre-mint
                           metadata must be tense-neutral - describe what the version
                           CONTAINS, never its deposit status.

  Exit 3 is deliberately distinct from exit 0: a gate that cannot run must not
  be mistaken for a gate that passed. Exit 4 is deliberately distinct from 1
  and 2: those are fixed by working, that one is not fixed at all.
#>
[CmdletBinding()]
param(
    [string] $RepoPath  = (Join-Path $PSScriptRoot ".."),
    [string] $ConceptId,
    [string] $ZenodoApi = "https://zenodo.org/api/records",
    [int]    $TimeoutSec = 25
)

$ErrorActionPreference = 'Continue'
$findings = @()
function Add-Finding([int]$Code, [string]$Label, [string]$Detail) {
    $script:findings += [pscustomobject]@{ Code = $Code; Label = $Label; Detail = $Detail }
}

$repo = Resolve-Path $RepoPath -ErrorAction SilentlyContinue
if (-not $repo) {
    Write-Host "  [CANNOT RUN] path not found: $RepoPath"
    exit 3
}
Write-Host "repo    : $repo"

git -C $repo rev-parse --git-dir *> $null
if ($LASTEXITCODE -ne 0) {
    Write-Host "  [CANNOT RUN] not a git repository: $repo"
    exit 3
}

# --- what version does this repository claim to be? --------------------------
# Two files declare it. They are read separately and compared, because a
# deposit whose own metadata disagrees about its identity has no version to
# check against Zenodo -- and picking one silently would choose which of two
# claims to believe.
$zPath = Join-Path $repo ".zenodo.json"
$cPath = Join-Path $repo "CITATION.cff"
$zVer = $null; $cVer = $null; $cDoi = $null; $zMeta = $null

if (Test-Path $zPath) {
    try { $zMeta = Get-Content $zPath -Raw | ConvertFrom-Json; $zVer = $zMeta.version } catch { $zVer = $null; $zMeta = $null }
}
if (Test-Path $cPath) {
    $cLines = Get-Content $cPath
    $m = $cLines | Where-Object { $_ -match '^version:\s*"?([^"\s]+)"?\s*$' } | Select-Object -First 1
    if ($m -match '^version:\s*"?([^"\s]+)"?\s*$') { $cVer = $Matches[1] }
    $d = $cLines | Where-Object { $_ -match '^doi:\s*"?(10\.\d+/zenodo\.(\d+))"?\s*$' } | Select-Object -First 1
    if ($d -match '^doi:\s*"?(10\.\d+/zenodo\.(\d+))"?\s*$') { $cDoi = $Matches[2] }
}

$canVersion = $true
if (-not $zVer -and -not $cVer) {
    # Not a reason to abort. Retrodicting this gate against tag v0.1.3 showed the
    # concept-DOI abort below suppressing the self-negating scan - a purely local
    # check, needing no network and no version, silenced by a missing Zenodo
    # prerequisite. A missing input for ONE check disables THAT check; only a
    # condition that makes the whole gate meaningless (no repo, no path) aborts.
    Add-Finding 3 "CANNOT RUN" "no version declared in .zenodo.json or CITATION.cff - the published-version and tag checks cannot run"
    $canVersion = $false
}
if ($zVer -and $cVer -and $zVer -ne $cVer) {
    Add-Finding 5 "VERSION CONFLICT" ".zenodo.json says '$zVer', CITATION.cff says '$cVer' - the deposit has no single identity"
}
$ver = if ($zVer) { $zVer } else { $cVer }
if (-not $ConceptId) { $ConceptId = $cDoi }
$canAskZenodo = $canVersion
if (-not $ConceptId) {
    Add-Finding 3 "CANNOT RUN" "no concept DOI found (CITATION.cff top-level 'doi:') and none supplied via -ConceptId - the already-published check cannot run"
    $canAskZenodo = $false
}
Write-Host "version : $(if ($ver) { $ver } else { '(none declared)' })  (zenodo.json='$zVer' citation.cff='$cVer')"
Write-Host "concept : $(if ($ConceptId) { "10.5281/zenodo.$ConceptId" } else { '(none)' })"

# --- 1. nothing uncommitted ---------------------------------------------------
$dirty = @(git -C $repo status --porcelain 2>$null | Where-Object { $_ })
if ($dirty.Count -gt 0) {
    Add-Finding 1 "DIRTY" "$($dirty.Count) uncommitted path(s); an upload would carry bytes that exist in no commit"
}

# --- 2. and on the server, asked of the server --------------------------------
$branch = git -C $repo rev-parse --abbrev-ref HEAD 2>$null
if (-not $branch -or $branch -eq "HEAD") {
    Add-Finding 3 "CANNOT RUN" "detached HEAD - no branch to compare against the server"
} else {
    $head = git -C $repo rev-parse HEAD 2>$null
    $ls = git -C $repo ls-remote origin "refs/heads/$branch" 2>$null
    if ($LASTEXITCODE -ne 0) {
        Add-Finding 3 "CANNOT RUN" "could not reach origin to ask for refs/heads/$branch - unreachable is not the same as in-sync"
    } elseif (-not $ls) {
        Add-Finding 3 "CANNOT RUN" "origin has no refs/heads/$branch - nothing to compare HEAD against"
    } else {
        $remoteSha = ($ls -split "`t")[0]
        if ($remoteSha -ne $head) {
            Add-Finding 2 "UNPUSHED" "server has $($remoteSha.Substring(0,7)) for $branch, local HEAD is $($head.Substring(0,7))"
        } else {
            Write-Host "server  : origin/$branch = $($head.Substring(0,7)) (asked of the server, not of a local cache)"
        }
    }
}

# --- 3. and Zenodo has not already published this version ---------------------
$latest = $null; $latestDoi = $null; $latestDate = $null
if (-not $canAskZenodo) {
    Write-Host "live    : (not asked - no concept DOI and/or no declared version)"
} else {
    try {
        $rec = Invoke-RestMethod "$ZenodoApi/$ConceptId" -TimeoutSec $TimeoutSec
        $latest = $rec.metadata.version; $latestDoi = $rec.doi; $latestDate = $rec.metadata.publication_date
    } catch { $latest = $null }

    if ($null -eq $latest) {
        Add-Finding 3 "CANNOT RUN" "Zenodo unreachable - this gate does not know whether v$ver is already published, and will not guess"
    } else {
        Write-Host "live    : v$latest  $latestDoi  ($latestDate)"
        $already = $false
        try { $already = ([version]$ver -le [version]$latest) } catch { $already = ($ver -eq $latest) }
        if ($already) {
            Add-Finding 4 "ALREADY PUBLISHED" "live latest is v$latest ($latestDoi, $latestDate); a second v$ver would be permanent and unwithdrawable"
        }
    }
}

# --- 4. and the content being deposited is reachable by a version tag ---------
# v1.0's own metadata records "published from git tag v0.1.3", and the file it
# shipped is that tag's archive. That provenance is a claim the record makes and
# nothing established. A deposit built from an untagged commit attaches bytes to
# a permanent DOI with no named point in history to rebuild them from.
if (-not $canVersion) {
    Write-Host "tag     : (not checked - no declared version to match a tag against)"
} else {
$tagsAtHead = @(git -C $repo tag --points-at HEAD 2>$null | Where-Object { $_ })
$verTag = $tagsAtHead | Where-Object { ($_ -replace '^v', '') -eq $ver }
if ($tagsAtHead.Count -eq 0) {
    $desc = git -C $repo describe --tags --abbrev=0 2>$null
    $behind = if ($desc) { git -C $repo rev-list --count "$desc..HEAD" 2>$null } else { $null }
    $where = if ($desc) { "latest tag is $desc, $behind commit(s) back" } else { "no tags in this repository" }
    Add-Finding 6 "NO VERSION TAG" "nothing tags HEAD, so the upload would name no point in history ($where)"
} elseif (-not $verTag) {
    Add-Finding 6 "NO VERSION TAG" "HEAD is tagged '$($tagsAtHead -join ", ")' but the deposit declares v$ver - the archive name and the record version would disagree"
} else {
    Write-Host "tag     : $verTag at HEAD (the archive the upload should carry)"
}
}

# --- 5. and the metadata does not assert that it has not been deposited ------- SELFNEG-OK
# Both prior deposits shipped a permanent, uncorrectable claim that they did not
# exist: v1.0's archive says "NOT YET DEPOSITED", v1.1's says "NOT YET MINTED". SELFNEG-OK
# The text is authored before the mint and the mint is what falsifies it, so
# there is no ordering that saves a tense-bound status label.
#
# Scanned across EVERY tracked file, not just .zenodo.json. The first version of
# this check read .zenodo.json alone - aimed at the file where the defect was
# found rather than at its shape - and the deposited v1.1 archive turned out to
# carry the same claim in CITATION.cff and README.md too. That is the exact
# error this check exists to catch, committed inside the check for it.
#
# The scanner must contain the phrases it searches for, so exemption is by an
# explicit per-line marker, and EVERY exemption is printed. A silent exclusion
# list would be a hole nobody could see; a visible one is a decision a reader
# can audit. Exempt lines are counted and reported even when the gate passes.
$selfNegating = @(
    'NOT YET MINTED', 'NOT YET DEPOSITED', 'not yet minted', 'not yet deposited',   # SELFNEG-OK
    'awaiting operator', 'will only exist after', 'not been deposited',             # SELFNEG-OK
    'to be minted', 'NOT YET PUBLISHED', 'not yet published'                        # SELFNEG-OK
)
$exemptMarker = 'SELFNEG-OK'
$tracked = @(git -C $repo ls-files 2>$null | Where-Object { $_ })
if ($tracked.Count -eq 0) {
    # Not "no phrases found" - no text was searched at all. A check that could not
    # run must never be reported, or defaulted, as a check that passed.
    Add-Finding 3 "CANNOT RUN" "no tracked files listed, so the self-negating-metadata check searched nothing"
} else {
    $snScanned = 0; $snEmpty = 0; $snExempt = 0; $snExemptFiles = @()
    foreach ($rel in $tracked) {
        $full = Join-Path $repo $rel
        if (-not (Test-Path $full)) { $snEmpty++; continue }
        $lines = @(Get-Content $full -ErrorAction SilentlyContinue)
        if ($lines.Count -eq 0) { $snEmpty++; continue }
        $snScanned++
        for ($i = 0; $i -lt $lines.Count; $i++) {
            $line = $lines[$i]
            foreach ($phrase in $selfNegating) {
                if (-not $line.Contains($phrase)) { continue }
                if ($line.Contains($exemptMarker)) {
                    $snExempt++
                    if ($snExemptFiles -notcontains $rel) { $snExemptFiles += $rel }
                    continue
                }
                $ctx = ($line -replace '\s+', ' ').Trim()
                if ($ctx.Length -gt 130) { $ctx = $ctx.Substring(0, 130) + "..." }
                Add-Finding 7 "SELF-NEGATING" "${rel}:$($i+1) contains ""$phrase"" - the deposited archive would permanently assert it was never made: $ctx"
            }
        }
    }
    if ($snScanned -eq 0) {
        Add-Finding 3 "CANNOT RUN" "no tracked file yielded any text, so the self-negating-metadata check searched nothing"
    } else {
        # Both numbers, always: "17 scanned" against 18 tracked is a gap a reader
        # would otherwise have to go and investigate to rule out.
        Write-Host "selfneg : $snScanned of $($tracked.Count) tracked file(s) scanned ($snEmpty empty/unreadable), $snExempt line(s) exempt via $exemptMarker$(if ($snExemptFiles) { " in $($snExemptFiles -join ', ')" })"
    }
}

# --- verdict ------------------------------------------------------------------
Write-Host ""
if ($findings.Count -eq 0) {
    Write-Host "MINT GATE: READY. v$ver is not yet published under concept 10.5281/zenodo.$ConceptId,"   # SELFNEG-OK
    Write-Host "  the tree is clean, HEAD is the commit the server holds for '$branch',"
    Write-Host "  and HEAD carries the tag '$verTag' the upload is named for."
    Write-Host "  This gate does not mint anything. The Publish action is the operator's."
    exit 0
}

foreach ($f in $findings) { Write-Host ("  [{0}] {1}" -f $f.Label, $f.Detail) }
Write-Host ""
# Most severe first: a terminal condition outranks one that cannot be determined,
# which outranks conditions the operator can fix by working.
foreach ($code in 4, 3, 5, 1, 2, 6, 7) {
    if ($findings.Code -contains $code) {
        Write-Host "MINT GATE: NOT READY - exiting $code (4=already published 3=cannot run 5=version conflict 1=dirty 2=unpushed 6=no version tag 7=self-negating metadata)"
        exit $code
    }
}
exit 3
