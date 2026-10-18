"""Resume the three large certificate checks with a bounded 30-minute budget each.

Keeps the original 60-second audit unchanged. This is executable RUP checking,
not a Lean proof. No SAT search or KEEP=112 worker is invoked.
"""
import subprocess
import time
from common import *


def main():
    rows={r['entry']:r for r in json.loads((OUT/'results.json').read_text())['entries']}
    destination=OUT/'large-proof-audit.json'
    records=[]
    if destination.exists():
        records=json.loads(destination.read_text())['entries']
    for entry in (258,133,256):
        row=rows[entry];attempt=ROOT/row['result'];attempt=attempt.parent
        identity=dict(certificate_sha256=sha(ROOT/row['certificate']),
                      checker_sha256=sha(HERE/'check_proof.py'),
                      formula_sha256=sha(ROOT/row['mapping']),
                      memory_mib=2048,wall_limit_seconds=1800)
        previous=next((r for r in records if r['entry']==entry),None)
        if previous and previous['identity']==identity and previous['status']=='PASSED_EXECUTABLE_RUP_CHECK':
            if sha(ROOT/previous['log'])==previous['log_sha256'] and sha(ROOT/previous['check_result'])==previous['check_result_sha256']:
                print(f'{entry}: reusing verified check',flush=True);continue
        logpath=attempt/'proof-check-1800s.log';start=time.perf_counter()
        print(f'{entry}: starting bounded RUP check',flush=True)
        with logpath.open('w',encoding='utf-8') as log:
            try:
                result=subprocess.run([sys.executable,str(HERE/'check_proof.py'),str(attempt)],
                    cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=1800)
                status='PASSED_EXECUTABLE_RUP_CHECK' if result.returncode==0 else 'CHECK_FAILED_OR_MEMORY_LIMIT'
                returncode=result.returncode
            except subprocess.TimeoutExpired:
                status='UNKNOWN_TIMEOUT';returncode=None
        record=dict(entry=entry,identity=identity,status=status,returncode=returncode,
                    seconds=time.perf_counter()-start,log=logpath.relative_to(ROOT).as_posix(),log_sha256=sha(logpath))
        if status=='PASSED_EXECUTABLE_RUP_CHECK':
            check=attempt/'drup-check.json'
            record.update(check_result=check.relative_to(ROOT).as_posix(),check_result_sha256=sha(check))
        records=[r for r in records if r['entry']!=entry]+[record]
        save(destination,dict(entries=records,scope='Executable RUP checking; not Lean verification; original 60-second audit retained'))
        print(json.dumps(record),flush=True)


if __name__=='__main__':main()
