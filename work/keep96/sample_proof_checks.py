"""Bounded survey certificate sample spanning observed UNSAT runtimes."""
import subprocess
from common import *


def main():
    table=json.loads((OUT/'survey-results.json').read_text())
    if not table['complete']:raise ValueError('finish survey first')
    rows=sorted((r for r in table['entries'] if r['status']=='UNSAT'),key=lambda r:(r['runtime_seconds'],r['entry']))
    count=min(12,len(rows))
    entries=[rows[round(i*(len(rows)-1)/max(1,count-1))]['entry'] for i in range(count)]
    save(OUT/'survey-proof-sample.json',dict(entries=entries,method='12 equally spaced rank quantiles of UNSAT runtime, ties by entry; outcome audit sample, not pilot selection',
        survey_sha256=sha(OUT/'survey-results.json'),proof_wall_limit_seconds=60,memory_mib=2048))
    if entries:subprocess.run([sys.executable,str(HERE/'audit_results.py'),'--phase','survey','--entries',*map(str,entries)],cwd=ROOT,check=True)


if __name__=='__main__':main()
