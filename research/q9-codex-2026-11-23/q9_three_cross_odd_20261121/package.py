import json,sys,zipfile,tempfile,subprocess
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parent
files={**{k:D/k for k in ['verify_bundle.py','replay.cpp','README.md','manifest.jsonl','catalogue.words.gz','summary.json','positive_verified.json']},'integer_checker.py':R/'verify_q9_intact98_all_crossings.py'}
for l in (D/'manifest.jsonl').read_text().splitlines():
    f=json.loads(l)['cert'];files[f]=D/f
archive=D/'three_cross_odd_certificates.zip'
with zipfile.ZipFile(archive,'w') as z:
    for k,v in sorted(files.items()):z.write(v,k,compress_type=zipfile.ZIP_STORED if v.suffix=='.gz' else zipfile.ZIP_DEFLATED)
with zipfile.ZipFile(archive) as z,tempfile.TemporaryDirectory() as td:
    assert z.testzip() is None and sorted(z.namelist())==sorted(files);z.extractall(td)
    subprocess.run([sys.executable,'-B','verify_bundle.py','--native',str(D/'replay')],cwd=td,check=True)
print('archive_bytes',archive.stat().st_size,'members',len(files))
