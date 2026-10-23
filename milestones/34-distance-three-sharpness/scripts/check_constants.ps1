$ErrorActionPreference='Stop'
$repo='E:\Snake-in-a-box'
$milestone="$repo\milestones\34-distance-three-sharpness"
$support=[System.IO.File]::ReadAllText("$repo\milestones\28-direct-share-certificates\build\latest.txt").Trim()
$build=[System.IO.File]::ReadAllText("$milestone\build\latest.txt").Trim()
$env:PATH='D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;'+$env:PATH
$prior=[System.IO.File]::ReadAllText("$repo\milestones\31-joint-counter-soundness\build\latest.txt").Trim()
$env:LEAN_PATH=@($build,$prior,$support,"$repo\milestones\20-middle-path-release\build","$repo\milestones\14-component-construction\build","$repo\milestones\07-window-223\lean\generated\geometry\support-ci2y7deg","$repo\work\spectral\.verification\strengthened-n8g3mwjy\core\.lake\build\lib\lean","$repo\work\spectral\.verification\strengthened-n8g3mwjy") -join ';'
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
    foreach ($name in @('OptimalConstants')) {
        $logpath="$milestone\logs\support-$name.log"
        lake env lean -R "$milestone\lean" -o "$build\$name.olean" "$milestone\lean\$name.lean" 2>&1 | Tee-Object $logpath
        $result=$LASTEXITCODE
        $contents=if (Test-Path $logpath) { [System.IO.File]::ReadAllText($logpath) } else { '' }
        [System.IO.File]::WriteAllText($logpath,$contents,[System.Text.UTF8Encoding]::new($false))
        if ($result -ne 0) { exit $result }
        Write-Output "Built $name"
    }
} finally { Pop-Location }
