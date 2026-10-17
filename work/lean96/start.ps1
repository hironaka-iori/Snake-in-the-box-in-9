param([int]$Workers = 3)
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path (Join-Path $PSScriptRoot '../..')).Path
$python = 'C:/Users/zhanb/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
# The Python runner holds an OS file lock; concurrent launch attempts exit safely.
$runner = Join-Path $PSScriptRoot 'campaign.py'
$stamp = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssffff')
Start-Process -FilePath $python -ArgumentList @('-X','utf8',('"'+$runner+'"'),"$Workers") -WorkingDirectory $repo -WindowStyle Hidden -RedirectStandardOutput (Join-Path $repo ('outputs/lean96/runner-'+$stamp+'.log')) -RedirectStandardError (Join-Path $repo ('outputs/lean96/runner-'+$stamp+'.stderr.log'))
try { Invoke-WebRequest 'http://127.0.0.1:52096/status.json' -UseBasicParsing -TimeoutSec 2 | Out-Null }
catch {
  Start-Process -FilePath $python -ArgumentList @('-X','utf8',('"'+(Join-Path $PSScriptRoot 'dashboard.py')+'"')) -WorkingDirectory $repo -WindowStyle Hidden
}
