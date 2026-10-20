$ErrorActionPreference = 'Stop'
$repo = 'E:\Snake-in-a-box'
$here = "$repo\milestones\22-internal-anchor-donors"
New-Item -ItemType Directory -Force "$here\build", "$here\logs", "$repo\milestones\23-parity-compatible-faces\logs" | Out-Null
$env:PATH = 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;' + $env:PATH
$env:LEAN_PATH = @(
    "$here\build",
    "$repo\milestones\20-middle-path-release\build",
    "$repo\milestones\14-component-construction\build",
    "$repo\milestones\07-window-223\lean\generated\geometry\support-ci2y7deg",
    "$repo\work\spectral\.verification\strengthened-n8g3mwjy\core\.lake\build\lib\lean",
    "$repo\work\spectral\.verification\strengthened-n8g3mwjy"
) -join ';'
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
    lake env lean --root="$repo\milestones\20-middle-path-release\lean" -o "$here\build\PairedSeed.olean" "$repo\milestones\20-middle-path-release\lean\PairedSeed.lean" 2>&1 | Tee-Object "$here\logs\paired-seed.log"
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    lake env lean "$here\lean\FullDonor.lean" 2>&1 | Tee-Object "$here\logs\full-donor.log"
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    lake env lean "$repo\milestones\23-parity-compatible-faces\lean\Targets.lean" 2>&1 | Tee-Object "$repo\milestones\23-parity-compatible-faces\logs\targets.log"
    $result = $LASTEXITCODE
} finally { Pop-Location }
exit $result
