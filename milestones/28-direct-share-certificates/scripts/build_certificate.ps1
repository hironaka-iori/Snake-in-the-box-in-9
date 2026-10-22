$ErrorActionPreference = 'Stop'
$repo='E:\Snake-in-a-box'
$milestone="$repo\milestones\28-direct-share-certificates"
$build=[System.IO.File]::ReadAllText("$milestone\build\latest.txt").Trim()
$env:PATH='D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;'+$env:PATH
$env:LEAN_PATH=@($build,"$repo\milestones\20-middle-path-release\build","$repo\milestones\14-component-construction\build","$repo\milestones\07-window-223\lean\generated\geometry\support-ci2y7deg","$repo\work\spectral\.verification\strengthened-n8g3mwjy\core\.lake\build\lib\lean","$repo\work\spectral\.verification\strengthened-n8g3mwjy") -join ';'
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
    $names=@('LratCheck','LratFast','LocalWindowBridge','LocalWindowCnf/ShareGap0','LocalWindowSat/ShareGap0')
    $names+=0..7 | ForEach-Object { "LocalWindowUnsat/ShareGap0/Data$_" }
    $names+=@('LocalWindowUnsat/ShareGap0/Check1','LocalWindowUnsat/ShareGap0/Check2','LocalWindowUnsat/ShareGap0','WindowExclusion')
    foreach ($name in $names) {
        $sourceRoot=if ($name -in @('LratCheck','LratFast','LocalWindowBridge')) { "$milestone\upstream" } else { "$milestone\lean" }
        $destination="$build\$name.olean"
        New-Item -ItemType Directory -Force (Split-Path $destination -Parent) | Out-Null
        $logpath="$milestone\logs\$($name.Replace('/','-')).log"
        # Completed, unchanged modules may be reused after a later module fails.
        if ((Test-Path $destination) -and ((Get-Item $destination).LastWriteTime -gt (Get-Item "$sourceRoot\$name.lean").LastWriteTime)) { Write-Output "Reused $name";continue }
        lake env lean -R $sourceRoot -o $destination "$sourceRoot\$name.lean" 2>&1 | Tee-Object $logpath
        $result=$LASTEXITCODE
        $contents=if (Test-Path $logpath) { [System.IO.File]::ReadAllText($logpath) } else { '' }
        [System.IO.File]::WriteAllText($logpath,$contents,[System.Text.UTF8Encoding]::new($false))
        if ($result -ne 0) { exit $result }
        Write-Output "Built $name"
    }
} finally { Pop-Location }
