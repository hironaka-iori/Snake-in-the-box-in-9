"""Check box provenance modules using the previously pinned support environment."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1]
OLD=HERE.parent/'87-retained-array-membership'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
module=sys.argv[1] if len(sys.argv)>1 else 'BoxWitness'
assert module in ['Boxes','DigitReconstruction','BoxWitness']
receipt=OLD/'data/NumericRetention-audit.json'
assert sha(receipt)=='364985551bcfdec435cd08bb258c7bfb705074b996d5384a597da7e6d468e4df'
support=json.loads(receipt.read_text())
assert support['status']=='PASS_EXECUTABLE_NUMERIC_RETENTION'
for folder,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
    assert sha(OLD/folder/('NumericRetention'+suffix))==support[key]
assert sha(OLD/'data/RetainedPredicates-support.json')==support['combined_support_sha256']
deps={}
for dep in (['Boxes','DigitReconstruction'] if module=='BoxWitness' else []):
    p=HERE/'data'/f'{dep}-audit.json';d=json.loads(p.read_text())
    assert d['status']=='PASS_LEAN_MODULE'
    for folder,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(HERE/folder/(dep+suffix))==d[key]
    deps[dep]=sha(p)
for folder in ['build','logs','data']:(HERE/folder).mkdir(exist_ok=True)
paths=[str(HERE/'build')]+support['paths']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
if log.exists():
    stamp=time.time_ns();log.rename(HERE/'logs'/f'{module}-{stamp}.log')
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=300)
row=dict(module=module,exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,numeric_retention_receipt_sha256=sha(receipt),combined_support_sha256=support['combined_support_sha256'],dependency_receipts=deps)
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(row,indent=2)+'\n')
if p.returncode:print(log.read_text()[-22000:]);raise SystemExit(p.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==src.read_text().count('#print axioms')
checked=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    checked.append(dict(theorem=name,axioms=values))
row.update(status='PASS_LEAN_MODULE',olean_sha256=sha(obj),theorem_audits=checked,scope='Generic box containment or rejection argument only. Finite coverage and its connection to saved rows remain separate. Existing combined support environment reused without recompilation.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(row,indent=2)+'\n')
print(module,'PASS',round(row['seconds'],3),'seconds;',len(checked),'audits',flush=True)
