$ErrorActionPreference='Stop'
$milestone='E:\Snake-in-a-box\milestones\37-logical-paper-rewrite'
$build=Join-Path "$milestone\build" ([Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $build,"$milestone\logs" | Out-Null
$env:PATH='D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;'+$env:PATH
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
 lake env lean -R "$milestone\lean" -o "$build\PaperArithmetic.olean" "$milestone\lean\PaperArithmetic.lean" 2>&1 | Tee-Object "$milestone\logs\PaperArithmetic.log"
 $result=$LASTEXITCODE
 if($result -ne 0){exit $result}
 [System.IO.File]::WriteAllText("$milestone\build\latest.txt",$build)
} finally { Pop-Location }
