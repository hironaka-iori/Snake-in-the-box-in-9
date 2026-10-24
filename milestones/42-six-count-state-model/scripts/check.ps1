$ErrorActionPreference='Stop'
$milestone='E:\Snake-in-a-box\milestones\42-six-count-state-model'
$build=Join-Path "$milestone\build" ([Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $build,"$milestone\logs" | Out-Null
$env:PATH='D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;'+$env:PATH
$env:LEAN_PATH=[System.IO.File]::ReadAllText('E:\Snake-in-a-box\milestones\41-joint-intervening-sum\build\latest.txt').Trim()
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
 lake env lean -R "$milestone\lean" -o "$build\CommonBudget.olean" "$milestone\lean\CommonBudget.lean" 2>&1 | Tee-Object "$milestone\logs\CommonBudget.log"
 $result=$LASTEXITCODE
 if($result -ne 0){exit $result}
 [System.IO.File]::WriteAllText("$milestone\build\latest.txt",$build)
} finally { Pop-Location }
