"""Reuse the inspected native replay with temporary proof writes on the system volume."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
source=ROOT/'milestones/114-total-count-pressure/scripts/certify_sum.py'
text=source.read_text(encoding='utf-8')
text=text.replace('import argparse, hashlib, importlib.util, json, subprocess, sys, time','import argparse, hashlib, importlib.util, json, os, shutil, subprocess, sys, tempfile, time')
old="work = HERE/'work'/args.case\nwork.mkdir(parents=True,exist_ok=True)"
new="""saved_work = HERE/'work'/args.case
saved_work.mkdir(parents=True,exist_ok=True)
work = Path(tempfile.mkdtemp(prefix='snake117-'+args.case+'-'))
def retain_work():
    for source_file in work.iterdir():
        if source_file.is_file():
            target_file=saved_work/source_file.name
            assert not target_file.exists()
            shutil.copyfile(source_file,target_file)
            assert sha(source_file)==sha(target_file)
"""
assert text.count(old)==1;text=text.replace(old,new)
old="stdout,stderr = HERE/'logs'/(args.case+'-solver.stdout.txt'),HERE/'logs'/(args.case+'-solver.stderr.txt')"
text=text.replace(old,old+"\nout.update(status='RUNNING',pid=os.getpid(),scratch=str(work),saved_work=saved_work.relative_to(HERE).as_posix())\nrecord.write_text(json.dumps(out,indent=2)+'\\n',encoding='utf-8')")
text=text.replace("if out['status'] != 'NATIVE_UNSAT_LEAN_PENDING':\n    sys.exit(0)","if out['status'] != 'NATIVE_UNSAT_LEAN_PENDING':\n    retain_work()\n    sys.exit(0)")
text=text.replace("(HERE/'data'/(args.case+'-certificate.json')).write_text", "retain_work()\n(HERE/'data'/(args.case+'-certificate.json')).write_text")
target=HERE/'scripts/certify_sum.py';assert not target.exists();target.write_text(text,encoding='utf-8')
(HERE/'data/certifier-source.json').write_text(json.dumps(dict(source=source.relative_to(ROOT).as_posix(),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),changes='Use system temporary output, verify byte-identical saved copies, record running PID; original contradiction replay preserved.'),indent=2)+'\n',encoding='utf-8')
print('Prepared native certificate and independent RUP replay; full Lean chain remains separate.')
