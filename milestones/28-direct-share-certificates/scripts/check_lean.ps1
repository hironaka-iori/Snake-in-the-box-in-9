$ErrorActionPreference = 'Stop'
$milestone = 'E:\Snake-in-a-box\milestones\28-direct-share-certificates'
$env:PATH = 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin;' + $env:PATH
Push-Location 'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib'
try {
    lake env lean "$milestone\lean\ShareArithmetic.lean" 2>&1 |
        Tee-Object "$milestone\logs\share-arithmetic.log"
    $result = $LASTEXITCODE
} finally {
    $path = "$milestone\logs\share-arithmetic.log"
    $contents = [System.IO.File]::ReadAllText($path)
    [System.IO.File]::WriteAllText($path,$contents,[System.Text.UTF8Encoding]::new($false))
    Pop-Location
}
exit $result
