import zipfile,json,sys,subprocess,tempfile
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parent
files={k:D/k for k in ('verify_bundle.py','emit_tables.cpp','replay.cpp','README.md','summary.json','manifest.jsonl','tree_manifest.jsonl')}
files.update({'catalogue.words.gz':R/'q9_three_cross_odd_20261121/catalogue.words.gz','integer_checker.py':R/'verify_q9_intact98_all_crossings.py','tree_replay.cpp':R/'q9_facet_priced_tree_20261121/replay.cpp'})
for key,name in [('cert','manifest.jsonl'),('tree','tree_manifest.jsonl')]:
    for l in (D/name).read_text().splitlines():
        p=json.loads(l)[key];files[p]=D/p
dest=D/'three_cross_same_certificates.zip'
with zipfile.ZipFile(dest,'w') as z:
    for n,p in sorted(files.items()):z.write(p,n,compress_type=zipfile.ZIP_STORED if n.endswith('.gz') else zipfile.ZIP_DEFLATED)
with zipfile.ZipFile(dest) as z,tempfile.TemporaryDirectory() as t:
    assert z.testzip() is None;z.extractall(t);subprocess.run([sys.executable,'-B','verify_bundle.py'],cwd=t,check=True)
print('archive_bytes',dest.stat().st_size,'members',len(files))
