param([string[]]$Modules=@('LocalWindowCnf/PairShareCert','LocalWindowSat/PairShareCert','LocalWindowUnsat/PairShareCert/Data0','LocalWindowUnsat/PairShareCert/Data1','LocalWindowUnsat/PairShareCert/Check1','LocalWindowUnsat/PairShareCert','LocalWindowShareBridge','ThreeSquareBonus','PairSharePacking'))
$ErrorActionPreference='Stop'
$repo='E:\Snake-in-a-box'
$milestone="$repo\milestones\35-equality-share-bonus"
$old=[System.IO.File]::ReadAllText("$milestone\build\latest.txt").Trim()
$build=Join-Path "$milestone\build" ([Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Force $build | Out-Null
Copy-Item "$old\*" $build -Recurse
[System.IO.File]::WriteAllText("$milestone\build\latest.txt",$build)
$paths=@($build)
foreach ($prior in @('33-distance-three-singletons','32-seven-count-four-screen','31-joint-counter-soundness','28-direct-share-certificates')) {
  $file=if ($prior -like '32-*') {'proofs-latest.txt'} else {'latest.txt'}
  $paths += [System.IO.File]::ReadAllText("$repo\milestones\$prior\build\$file").Trim()
}
# Lean resolves a shared namespace directory in the first matching root.
# Merge the prior pair modules into this fresh root without replacing new files.
$pairRoot=$paths[1]
Get-ChildItem -LiteralPath $pairRoot -Recurse -File -Filter '*.olean' | ForEach-Object {
  $relative=$_.FullName.Substring($pairRoot.Length+1)
  $destination=Join-Path $build $relative
  if(-not(Test-Path $destination)) {
    New-Item -ItemType Directory -Force (Split-Path $destination) | Out-Null
    Copy-Item -LiteralPath $_.FullName -Destination $destination
  }
}
$env:LEAN_PATH=($paths+@("$repo\milestones\20-middle-path-release\build","$repo\milestones\14-component-construction\build","$repo\milestones\07-window-223\lean\generated\geometry\support-ci2y7deg","$repo\work\spectral\.verification\strengthened-n8g3mwjy\core\.lake\build\lib\lean","$repo\work\spectral\.verification\strengthened-n8g3mwjy")) -join ';'
$env:PATH='D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;'+$env:PATH
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
 foreach ($name in $Modules) {
  $root=if($name -eq 'LocalWindowShareBridge'){"$milestone\upstream"}else{"$milestone\lean"}
  $out="$build\$name.olean"
  New-Item -ItemType Directory -Force (Split-Path $out) | Out-Null
  if(Test-Path $out){Remove-Item -LiteralPath $out}
  $log="$milestone\logs\check-$($name.Replace('/','-')).log"
  lake env lean -R $root -o $out "$root\$name.lean" 2>&1 | Tee-Object $log
  $result=$LASTEXITCODE
  $contents=if(Test-Path $log){[System.IO.File]::ReadAllText($log)}else{''}
  [System.IO.File]::WriteAllText($log,$contents,[System.Text.UTF8Encoding]::new($false))
  if($result -ne 0){exit $result}
  Write-Output "Built $name"
 }
}finally{Pop-Location}
