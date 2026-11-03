$ErrorActionPreference = 'Stop'
$taskRoot = 'E:\Snake-in-a-box\milestones\146-initial-tree-and-paper'
$output = Join-Path $taskRoot 'data/semantic-pilot-timing.json'
$result = [ordered]@{
  status = 'OBSERVING'
  scope = 'Read-only Windows process timestamps; no Lean process is launched by this observer.'
  first_module = [ordered]@{
    module = 'LocalWindowCnf.ShareWindow146'
    checker_created_utc = '2026-11-03T19:02:12.912411Z'
    preflight_end_run_timestamp_ns = '1793732542802651700'
    preflight_seconds_to_run_stamp = 9.8902407
    last_live_compiler_sample_seconds = 71.67099999999846
    receipt_seconds_including_postflight = 182.85900000000038
    exact_compiler_seconds = $null
    note = 'The checker did not record compiler exit separately; do not call its combined elapsed value compiler time.'
  }
  observed_modules = @()
}
function Save-Timing {
  $result.updated_utc = [DateTime]::UtcNow.ToString('o')
  $result | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $output -Encoding utf8
}
Save-Timing
$deadline = [DateTime]::UtcNow.AddMinutes(20)
while ([DateTime]::UtcNow -lt $deadline) {
  $progress = Get-Content -LiteralPath (Join-Path $taskRoot 'data/semantic-progress.json') -Raw | ConvertFrom-Json
  if ($progress.status -ne 'RUNNING') { $result.status = 'FINISHED'; Save-Timing; break }
  $active = $progress.active
  if ($null -eq $active -or $active.module -notin @('Share146.Data','Share146.Structure') -or
      $active.module -in @($result.observed_modules.module)) { Start-Sleep -Seconds 1; continue }
  $recordFolder = Get-ChildItem -LiteralPath (Join-Path $taskRoot 'logs') -Directory -Filter ($active.module + '-*') |
    Sort-Object Name -Descending | Select-Object -First 1
  if ($null -eq $recordFolder) { Start-Sleep -Seconds 1; continue }
  $recordFile = Join-Path $recordFolder.FullName 'record.json'
  if (-not (Test-Path -LiteralPath $recordFile)) { Start-Sleep -Seconds 1; continue }
  try { $record = Get-Content -LiteralPath $recordFile -Raw | ConvertFrom-Json } catch { Start-Sleep -Seconds 1; continue }
  if ($record.pid -ne $active.pid) { Start-Sleep -Seconds 1; continue }
  $children = @(Get-CimInstance Win32_Process -Filter "Name='lean.exe'" |
    Where-Object { $_.ParentProcessId -eq $record.launcher_pid })
  if ($children.Count -eq 0) { Start-Sleep -Seconds 1; continue }
  if ($children.Count -ne 1) { throw 'Expected one owned Lean process' }
  $checker = Get-Process -Id $active.pid
  $compiler = Get-Process -Id $children[0].ProcessId
  $null = $compiler.Handle
  $compilerStart = $compiler.StartTime.ToUniversalTime()
  $entry = [ordered]@{
    module = $active.module
    checker_pid = $active.pid
    compiler_pid = $compiler.Id
    checker_created_utc = $checker.StartTime.ToUniversalTime().ToString('o')
    compiler_created_utc = $compilerStart.ToString('o')
    preflight_seconds_to_compiler_start = ($compilerStart - $checker.StartTime.ToUniversalTime()).TotalSeconds
    compiler_finished_utc = $null
    compiler_seconds = $null
    record = $recordFile
  }
  $result.observed_modules += $entry
  Save-Timing
  while (-not $compiler.HasExited) { Start-Sleep -Milliseconds 500; $compiler.Refresh() }
  $compiler.WaitForExit()
  $compilerEnd = $compiler.ExitTime.ToUniversalTime()
  $entry.compiler_finished_utc = $compilerEnd.ToString('o')
  $entry.compiler_seconds = ($compilerEnd - $compilerStart).TotalSeconds
  Save-Timing
  Write-Output ($entry | ConvertTo-Json -Compress)
}
if ($result.status -eq 'OBSERVING') { $result.status = 'OBSERVER_DEADLINE'; Save-Timing }
