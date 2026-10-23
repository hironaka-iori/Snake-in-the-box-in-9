$ErrorActionPreference='Stop'
$root='E:\Snake-in-a-box\milestones\32-seven-count-four-screen'
$build=Join-Path "$root\build" ([Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $build | Out-Null
[System.IO.File]::WriteAllText("$root\build\latest.txt",$build)
$env:PATH='D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;'+$env:PATH
$env:LEAN_PATH=$build
foreach ($name in @('WindowAutomatonDefs','FamilyCoverage')) {
    $source=if ($name -eq 'WindowAutomatonDefs') { "$root\upstream\$name.lean" } else { "$root\lean\$name.lean" }
    $sourceRoot=Split-Path $source -Parent
    $log="$root\logs\$name.log"
    lean -R $sourceRoot -o "$build\$name.olean" $source 2>&1 | Tee-Object $log
    $result=$LASTEXITCODE
    $contents=if (Test-Path $log) { [System.IO.File]::ReadAllText($log) } else { '' }
    [System.IO.File]::WriteAllText($log,$contents,[System.Text.UTF8Encoding]::new($false))
    if ($result -ne 0) { exit $result }
}
