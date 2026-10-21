param([switch]$ReuseDependency)
$ErrorActionPreference = 'Stop'
$repo = 'E:\Snake-in-a-box'
$milestone = "$repo\milestones\27-empty-square-packing"
$build = Join-Path "$milestone\build" ([Guid]::NewGuid().ToString('N'))
if ($ReuseDependency) {
    $build = (Get-ChildItem "$milestone\build" -Directory | Where-Object { Test-Path (Join-Path $_.FullName 'ShareCharge.olean') } | Sort-Object LastWriteTime -Descending | Select-Object -First 1).FullName
}
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
    if (-not $ReuseDependency) {
        lake env lean -R "$milestone\upstream" -o "$build\ShareCharge.olean" "$milestone\upstream\ShareCharge.lean" 2>&1 |
            Tee-Object "$milestone\logs\share-charge.log"
        if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    }
    lake env lean "$milestone\lean\SharePacking.lean" 2>&1 |
        Tee-Object "$milestone\logs\share-packing.log"
    $result = $LASTEXITCODE
} finally {
    foreach ($name in @('share-charge.log','share-packing.log')) {
        $logpath = Join-Path "$milestone\logs" $name
        if (Test-Path -LiteralPath $logpath) {
            $contents = [System.IO.File]::ReadAllText($logpath)
            [System.IO.File]::WriteAllText($logpath, $contents, [System.Text.UTF8Encoding]::new($false))
        }
    }
    Pop-Location
}
exit $result
