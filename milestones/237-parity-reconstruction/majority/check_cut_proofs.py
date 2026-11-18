"""Kernel-check the integer cuts, one small module at a time."""
from hashlib import sha256
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import time

here = Path(__file__).resolve().parent
lean = Path(sys.argv[1]).resolve()
def digest(path):
    return sha256(path.read_bytes()).hexdigest()

report = dict(version=subprocess.check_output([lean,'--version'],text=True).strip(),
              kernel_option='decide +kernel', checker=digest(Path(__file__)),
              input_hashes={p:digest(here/p) for p in ('cuts.json','decisions.json','CubeCut.lean')},
              modules=[])
with tempfile.TemporaryDirectory() as tmp:
    env = dict(os.environ,LEAN_PATH=tmp)
    def run(source, output):
        start=time.monotonic()
        result=subprocess.run([lean,'-j1','-o',str(output),str(source)],cwd=here,
                              env=env,text=True,capture_output=True)
        if result.returncode or result.stdout or result.stderr:
            raise RuntimeError((source.name,result.returncode,result.stdout,result.stderr))
        return dict(file=source.name,sha256=digest(source),seconds=round(time.monotonic()-start,3))
    report['checker_module']=run(here/'CubeCut.lean',Path(tmp)/'CubeCut.olean')
    for source in sorted((here/'certificates').glob('Cuts*.lean')):
        row=run(source,Path(tmp)/(source.stem+'.olean'))
        row['theorems']=source.read_text().count(':= by decide +kernel')
        report['modules'].append(row)
        print(source.name,row['theorems'],flush=True)
assert sum(r['theorems'] for r in report['modules'])==623
report['status']='PASS'
(here/'kernel-cuts.json').write_text(json.dumps(report,indent=2)+'\n')
