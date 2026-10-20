$ErrorActionPreference = 'Stop'
$repo = 'E:\Snake-in-a-box'
$milestone = "$repo\milestones\25-alternative-fillings"
$build = Join-Path "$milestone\build" ([Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force "$milestone\logs",$build | Out-Null
$env:PATH = 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;' + $env:PATH
$env:LEAN_PATH = @(
    $build,
    "$repo\milestones\20-middle-path-release\build",
    "$repo\milestones\14-component-construction\build",
    "$repo\milestones\07-window-223\lean\generated\geometry\support-ci2y7deg",
    "$repo\work\spectral\.verification\strengthened-n8g3mwjy\core\.lake\build\lib\lean",
    "$repo\work\spectral\.verification\strengthened-n8g3mwjy"
) -join ';'
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
    lake env lean -R "$repo\milestones\24-contracted-face-search\lean" -o "$build\Rigidity.olean" "$repo\milestones\24-contracted-face-search\lean\Rigidity.lean" 2>&1 |
        Tee-Object "$milestone\logs\rigidity-dependency.log"
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    lake env lean "$milestone\lean\Diversity.lean" 2>&1 |
        Tee-Object "$milestone\logs\diversity.log"
    $result = $LASTEXITCODE
} finally { Pop-Location }
exit $result
