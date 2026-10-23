$ErrorActionPreference='Stop'
$repo='E:\Snake-in-a-box'
$milestone="$repo\milestones\32-seven-count-four-screen"
$support=[System.IO.File]::ReadAllText("$repo\milestones\28-direct-share-certificates\build\latest.txt").Trim()
$build=Join-Path "$milestone\build" ([Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $build | Out-Null
[System.IO.File]::WriteAllText("$milestone\build\proofs-latest.txt",$build)
$env:PATH='D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;'+$env:PATH
$env:LEAN_PATH=@($build,$support,"$repo\milestones\20-middle-path-release\build","$repo\milestones\14-component-construction\build","$repo\milestones\07-window-223\lean\generated\geometry\support-ci2y7deg","$repo\work\spectral\.verification\strengthened-n8g3mwjy\core\.lake\build\lib\lean","$repo\work\spectral\.verification\strengthened-n8g3mwjy") -join ';'
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
    foreach ($name in @('WindowAutomatonDefs','WindowAutomatonData','WindowAutomatonLemmas','WindowAutomatonSequence','WindowAutomatonBridge','LocalWindowDirModel','LocalWindowDirKeys','LocalWindowDirBridge','DirectionWindowBridge')) {
        $logpath="$milestone\logs\support-$name.log"
        lake env lean -R "$milestone\upstream" -o "$build\$name.olean" "$milestone\upstream\$name.lean" 2>&1 | Tee-Object $logpath
        $result=$LASTEXITCODE
        $contents=if (Test-Path $logpath) { [System.IO.File]::ReadAllText($logpath) } else { '' }
        [System.IO.File]::WriteAllText($logpath,$contents,[System.Text.UTF8Encoding]::new($false))
        if ($result -ne 0) { exit $result }
        Write-Output "Built $name"
    }
} finally { Pop-Location }
