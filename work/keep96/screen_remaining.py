"""After a promising completed pilot, screen the other entries once at 10 seconds.

This changes only the computation budget, never KEEP=96 or the 193-vertex target.
"""
import subprocess
from common import *


def main():
    pilot=json.loads((OUT/'pilot-results.json').read_text())
    if not pilot['complete'] or len(pilot['entries'])!=12:
        raise ValueError('finish the twelve-entry pilot first')
    solved=sum(r['status']=='UNSAT' for r in pilot['entries'])
    fast=sum(r['status']=='UNSAT' and r['runtime_seconds']<10 for r in pilot['entries'])
    if solved<9 or fast<6:
        raise ValueError('pilot does not meet screening gate: >=9 UNSAT, >=6 under 10 seconds')
    chosen={r['entry'] for r in pilot['entries']};remaining=[i for i in range(262) if i not in chosen]
    decision=dict(pilot_unsat=solved,pilot_unsat_under10s=fast,entries=remaining,
                  seconds_per_entry=10,memory_mib=2048,maximum_worker_seconds=2500,
                  reason='Most pilot cases were excluded quickly, but some took minutes and yielded large proofs. Screen the remaining 250 once with a shorter cap; leave hard cases UNKNOWN rather than escalating.',
                  target_vertices=193,keep=96,pilot_results_sha256=sha(OUT/'pilot-results.json'))
    save(OUT/'scaling-decision.json',decision)
    command=[sys.executable,str(HERE/'run.py'),'--phase','survey','--seconds','10','--memory-mib','2048','--entries',*map(str,remaining)]
    subprocess.run(command,cwd=ROOT,check=True)


if __name__=='__main__':main()
