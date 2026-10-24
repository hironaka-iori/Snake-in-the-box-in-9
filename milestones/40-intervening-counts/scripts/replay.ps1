param([int]$Case=401)
$ErrorActionPreference='Stop'
$repo='E:\Snake-in-a-box'
$milestone="$repo\milestones\40-intervening-counts"
$support=[System.IO.File]::ReadAllText("$repo\milestones\28-direct-share-certificates\build\latest.txt").Trim()
$build=Join-Path "$milestone\build" ([Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $build | Out-Null
if (Test-Path "$milestone\build\latest.txt") {
    $old=[System.IO.File]::ReadAllText("$milestone\build\latest.txt").Trim()
    Copy-Item "$old\*" $build -Recurse
}
[System.IO.File]::WriteAllText("$milestone\build\latest.txt",$build)
$env:PATH='D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;'+$env:PATH
$prior=[System.IO.File]::ReadAllText("$repo\milestones\31-joint-counter-soundness\build\latest.txt").Trim()
$norm=[System.IO.File]::ReadAllText("$repo\milestones\32-seven-count-four-screen\build\proofs-latest.txt").Trim()
$env:LEAN_PATH=@($build,$prior,$norm,$support,"$repo\milestones\20-middle-path-release\build","$repo\milestones\14-component-construction\build","$repo\milestones\07-window-223\lean\generated\geometry\support-ci2y7deg","$repo\work\spectral\.verification\strengthened-n8g3mwjy\core\.lake\build\lib\lean","$repo\work\spectral\.verification\strengthened-n8g3mwjy") -join ';'
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
    $mod="CycleWindow$Case"
    $names=@("LocalWindowCnf/$mod","LocalWindowSat/$mod")
    $names+=Get-ChildItem "$milestone\lean\LocalWindowUnsat\$mod\Data*.lean" | Sort-Object { [int]($_.BaseName.Substring(4)) } | ForEach-Object { "LocalWindowUnsat/$mod/$($_.BaseName)" }
    $names+=Get-ChildItem "$milestone\lean\LocalWindowUnsat\$mod\Check*.lean" | Sort-Object { [int]($_.BaseName.Substring(5)) } | ForEach-Object { "LocalWindowUnsat/$mod/$($_.BaseName)" }
    $names+=@("LocalWindowUnsat/$mod","CycleExclusion$Case")
    foreach ($name in $names) {
        $dest="$build\$name.olean"
        New-Item -ItemType Directory -Force (Split-Path $dest -Parent) | Out-Null
        if(Test-Path $dest){Remove-Item -LiteralPath $dest}
        $logpath="$milestone\logs\$($name.Replace('/','-')).log"
        lake env lean -R "$milestone\lean" -o $dest "$milestone\lean\$name.lean" 2>&1 | Tee-Object $logpath
        $result=$LASTEXITCODE
        $contents=if (Test-Path $logpath) { [System.IO.File]::ReadAllText($logpath) } else { '' }
        [System.IO.File]::WriteAllText($logpath,$contents,[System.Text.UTF8Encoding]::new($false))
        if ($result -ne 0) { exit $result }
        Write-Output "Built $name"
    }
} finally { Pop-Location }
