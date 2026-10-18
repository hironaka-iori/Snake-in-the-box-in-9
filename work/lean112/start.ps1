param(
    [Parameter(Mandatory=$true)][string]$PythonExe,
    [Parameter(Mandatory=$true)][string]$LeanBin
)
$ErrorActionPreference='Stop'
$repo=Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
Set-Location -LiteralPath $repo
$env:PATH=$LeanBin+';'+$env:PATH
$logs=Join-Path $repo 'outputs/lean112'
New-Item -ItemType Directory -Path $logs -Force | Out-Null
$stamp=Get-Date -Format 'yyyyMMdd-HHmmss'
& $PythonExe -u (Join-Path $PSScriptRoot 'service.py') --lean-bin $LeanBin --port 51993 1>> (Join-Path $logs "service-$stamp.stdout.log") 2>> (Join-Path $logs "service-$stamp.stderr.log")
exit $LASTEXITCODE
