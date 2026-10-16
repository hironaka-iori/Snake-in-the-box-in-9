"""Audit saved formulas/models and bounded executable UNSAT certificates."""
import argparse
import subprocess
import time
from common import *


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--phase',default='pilot');ap.add_argument('--proof-seconds',type=float,default=60)
    ap.add_argument('--entries',type=int,nargs='+',help='check only these entries, preserving other existing checks')
    a=ap.parse_args();table=json.loads((OUT/f'{a.phase}-results.json').read_text())
    path=OUT/f'{a.phase}-evidence-audit.json';records=[]
    if a.entries and path.exists():
        previous=json.loads(path.read_text())
        if previous['checker_sha256']!=sha(HERE/'check_proof.py') or previous['proof_wall_limit_seconds']!=a.proof_seconds:
            raise ValueError('existing checks have a different checker or limit')
        records=[r for r in previous['entries'] if r['entry'] not in a.entries]
    for row in table['entries']:
        if a.entries and row['entry'] not in a.entries:continue
        for p,h in row['artifact_hashes'].items():
            if sha(ROOT/p)!=h:raise ValueError('changed evidence: '+p)
        attempt=ROOT/row['attempt'];r=dict(entry=row['entry'],status=row['status'],artifact_hashes='PASSED',result_sha256=sha(attempt/'result.json'))
        if row['status']=='UNSAT':
            start=time.perf_counter()
            with (attempt/'proof-check.log').open('w',encoding='utf-8') as log:
                try:
                    process=subprocess.run([sys.executable,str(HERE/'check_proof.py'),str(attempt)],
                                           cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=a.proof_seconds)
                    r['proof_check']='PASSED_EXECUTABLE_RUP_CHECK' if process.returncode==0 else 'CHECK_FAILED_OR_UNSUPPORTED'
                    r['returncode']=process.returncode
                except subprocess.TimeoutExpired:
                    r['proof_check']='UNKNOWN_TIMEOUT'
            r['proof_check_seconds']=time.perf_counter()-start
            r['proof_check_log']=(attempt/'proof-check.log').relative_to(ROOT).as_posix()
            r['proof_check_log_sha256']=sha(attempt/'proof-check.log')
        records.append(r)
        save(path,dict(phase=a.phase,entries=records,proof_wall_limit_seconds=a.proof_seconds,
                       checker_sha256=sha(HERE/'check_proof.py'),scope='Executable checks, not Lean proofs'))
        print(json.dumps(r),flush=True)


if __name__=='__main__':main()
