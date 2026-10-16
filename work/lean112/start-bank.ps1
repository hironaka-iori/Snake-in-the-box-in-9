$ErrorActionPreference='Stop'
$taskRoot=Split-Path (Split-Path $PSScriptRoot -Parent) -Parent
$taskPython='C:\Users\tommy\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$taskOutput=Join-Path $taskRoot 'outputs\lean112'
$taskState=Join-Path $taskOutput 'bank-runner.json'
if(Test-Path -LiteralPath $taskState){
  $taskRecord=Get-Content -LiteralPath $taskState -Raw | ConvertFrom-Json
  if($taskRecord.status -eq 'RUNNING' -and (Get-Process -Id $taskRecord.pid -ErrorAction SilentlyContinue)){
    Write-Output "Proof runner already active: $($taskRecord.pid)"
    exit 0
  }
}
$taskScript=Join-Path $PSScriptRoot 'run_bank.py'
$taskProcess=Start-Process -FilePath $taskPython -ArgumentList @('-u',('"'+$taskScript+'"'),'--workers','2') -WorkingDirectory $taskRoot -WindowStyle Hidden -RedirectStandardOutput (Join-Path $taskOutput 'bank-runner.stdout.log') -RedirectStandardError (Join-Path $taskOutput 'bank-runner.stderr.log') -PassThru
Write-Output "Started proof runner: $($taskProcess.Id)"
