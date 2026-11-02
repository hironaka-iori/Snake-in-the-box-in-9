"""Resume the stopped replay with a longer timeout and unchanged proof sources."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
CASE = ROOT / 'milestones/73-countfree-share-catalogue/cases/case7302'
driver = CASE / 'scripts/complete_share.py'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
original = driver.read_bytes()
assert sha(original) == 'cbcf42c56b21bef21e2835c6325ed3289ed522b6d7bce695f0c6ef77a588ddb5'
command = ("@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' "
           "-and ($_.CommandLine -like '*case7302*' -or $_.CommandLine -like '*resume7302*') "
           f"-and $_.ProcessId -ne {os.getpid()} "
           "} | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress")
output = subprocess.check_output(['powershell', '-NoProfile', '-Command', command], text=True).strip()
active = json.loads(output) if output else []
assert not active, ('Existing replay process; do not duplicate it', active)
before = (CASE / 'logs/completion-record.json').read_bytes()
rows = json.loads(before)['records']
assert rows[-1]['module'] == 'LocalWindowUnsat/ShareWindow7302/Check66'
assert rows[-1]['exit_code'] == 1
saved = HERE / 'data/case7302-before-unique-resume.json'
assert not saved.exists(), 'Preserved initial replay snapshot already exists; inspect actual state before another resume'
saved.write_bytes(before)
(HERE / 'data/case7302-original-driver-unique.py.txt').write_bytes(original)
log = CASE / 'logs/LocalWindowUnsat-ShareWindow7302-Check66.log'
(HERE / 'logs/case7302-Check66-output-error.log').write_bytes(log.read_bytes())
assert 'failed to delete' in log.read_text()
text = original.decode('utf-8')
assert text.count('timeout=300') == 1
assert text.count("dest.with_suffix('.fresh.olean')") == 2
fresh_suffix = '.fresh-89-' + str(time.time_ns()) + '.olean'
adapted = text.replace('timeout=300', 'timeout=900').replace("dest.with_suffix('.fresh.olean')", 'dest.with_suffix(' + repr(fresh_suffix) + ')')
report = dict(status='RUNNING_RESUMED_REPLAY', pid=os.getpid(),
              started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              original_driver_sha256=sha(original), adapted_driver_sha256=sha(adapted.encode()),
              before_record_sha256=sha(before), timeout_log_sha256=sha(log.read_bytes()),
              timeout_seconds=900, fresh_file_suffix=fresh_suffix, no_existing_replay_process=True,
              prior_successful_rows=sum(r['exit_code'] == 0 for r in rows),
              scope='Timeout and unique temporary output path change. Original dependency/hash-based resume logic is reused; '
                    'proof sources and completed proof objects are unchanged. No final share theorem implied.')
rp = HERE / 'logs/case7302-unique-resume-run.json'
rp.write_text(json.dumps(report, indent=2) + '\n')
print('RESUME_CHECK66_WITH_UNIQUE_OUTPUT_AND_900_SECOND_LIMIT', report['prior_successful_rows'], 'prior successful rows', flush=True)
sys.argv = [str(driver)]
try:
    exec(compile(adapted, str(driver), 'exec'), {'__name__': '__main__', '__file__': str(driver)})
except BaseException as exc:
    report['status'] = 'RESUMED_DRIVER_STOPPED'
    report['exception'] = repr(exc)
    raise
else:
    report['status'] = 'RESUMED_DRIVER_COMPLETED_AUDIT_PENDING'
finally:
    report['stopped_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    rp.write_text(json.dumps(report, indent=2) + '\n')
