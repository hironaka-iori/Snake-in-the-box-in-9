param([string[]]$Modules=@('MultiCentreCount'))
$ErrorActionPreference='Stop'
$repo='E:\Snake-in-a-box'
$milestone="$repo\milestones\41-joint-intervening-sum"
$build=Join-Path "$milestone\build" ([Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $build,"$milestone\logs" | Out-Null
if(Test-Path "$milestone\build\latest.txt") {
 $old=[System.IO.File]::ReadAllText("$milestone\build\latest.txt").Trim()
 Copy-Item "$old\*" $build -Recurse
}
$paths=@($build)
foreach ($prior in @('36-critical-cycle-consistency','33-distance-three-singletons','32-seven-count-four-screen','31-joint-counter-soundness','28-direct-share-certificates')) {
 $file=if($prior -like '32-*'){'proofs-latest.txt'}else{'latest.txt'}
 $paths += [System.IO.File]::ReadAllText("$repo\milestones\$prior\build\$file").Trim()
}
$prior36=$paths[1]
Get-ChildItem -LiteralPath $prior36 -Recurse -File -Filter '*.olean' | ForEach-Object {
 $relative=$_.FullName.Substring($prior36.Length+1)
 $dest=Join-Path $build $relative
 if(-not(Test-Path $dest)) {
  New-Item -ItemType Directory -Force (Split-Path $dest) | Out-Null
  Copy-Item -LiteralPath $_.FullName -Destination $dest
 }
}
$env:LEAN_PATH=($paths+@("$repo\milestones\20-middle-path-release\build","$repo\milestones\14-component-construction\build","$repo\milestones\07-window-223\lean\generated\geometry\support-ci2y7deg","$repo\work\spectral\.verification\strengthened-n8g3mwjy\core\.lake\build\lib\lean","$repo\work\spectral\.verification\strengthened-n8g3mwjy")) -join ';'
$env:PATH='D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;'+$env:PATH
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
 foreach($name in $Modules) {
  $out="$build\$name.olean"
  if(Test-Path $out){Remove-Item -LiteralPath $out}
  lake env lean -R "$milestone\lean" -o $out "$milestone\lean\$name.lean" 2>&1 | Tee-Object "$milestone\logs\$name.log"
  if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
 }
 [System.IO.File]::WriteAllText("$milestone\build\latest.txt",$build)
} finally {Pop-Location}
