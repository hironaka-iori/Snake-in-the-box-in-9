param(
    [Parameter(Mandatory=$true)][string]$PythonExe,
    [Parameter(Mandatory=$true)][string]$LeanBin,
    [int]$Workers = 3
)
$ErrorActionPreference = 'Stop'
$repo = Split-Path -Parent $PSScriptRoot
$folder = Join-Path $repo 'work/lean'
$taskLock = $null
try {
    $taskLock = [System.IO.File]::Open((Join-Path $folder 'background144.lock'),
        [System.IO.FileMode]::OpenOrCreate, [System.IO.FileAccess]::ReadWrite,
        [System.IO.FileShare]::None)
    Set-Location -LiteralPath $repo
    $env:PATH = $LeanBin + ';' + $env:PATH
    $stamp = Get-Date -Format 'yyyyMMdd-HHmmss'
    $stdout = Join-Path $folder "background144-$stamp.stdout.log"
    $stderr = Join-Path $folder "background144-$stamp.stderr.log"
    $launcherStatus = Join-Path $folder 'background144-launcher.json'
    [pscustomobject]@{ Status='RUNNING'; LauncherPid=$PID; StartedUtc=[DateTime]::UtcNow.ToString('o'); Stdout=$stdout; Stderr=$stderr } |
        ConvertTo-Json | Set-Content -LiteralPath $launcherStatus -Encoding UTF8
    & $PythonExe -u work/check_lean_certificates.py 144v2 --workers $Workers `
        --results-module DfsBankCert144Results `
        --audit-theorem Snake9.Dfs.bank_no_long_prefix_keep144 `
        --audit-theorem Snake9.Dfs.bank_no_long_suffix_keep144 `
        --audit-theorem Snake9.Dfs.bank_end_segment_length_le191 1>> $stdout 2>> $stderr
    $workerExit = $LASTEXITCODE
    [pscustomobject]@{ Status= $(if ($workerExit -eq 0) { 'PASSED' } else { 'FAILED' }); ExitCode=$workerExit; FinishedUtc=[DateTime]::UtcNow.ToString('o'); Stdout=$stdout; Stderr=$stderr } |
        ConvertTo-Json | Set-Content -LiteralPath $launcherStatus -Encoding UTF8
    exit $workerExit
} finally {
    if ($null -ne $taskLock) { $taskLock.Dispose() }
}
