"""Check generic soundness of bounded reference-shape cache reuse."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1]
PREV=HERE.parent/'90-context-witness-certificates'
P89=HERE.parent/'89-shared-cover-certification'
P88=HERE.parent/'88-retention-diagram-certificate'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
receipt=PREV/'data/WitnessFactors-audit.json'
assert sha(receipt)=='cb4e7ad98703f669a7b84339e4f2fd226593f5db8b3555d2560fc9cce63db727'
support=json.loads(receipt.read_text())
assert support['status']=='PASS_GENERIC_WITNESS_FACTORIZATION'
deps={'WitnessFactors':sha(receipt)}
for folder,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
    assert sha(PREV/folder/('WitnessFactors'+suffix))==support[key]
for name,expected in support['dependency_receipts'].items():
    root=PREV if name=='WitnessLookup' else P89 if name in ['SharedAssembly','ContextTransport'] else P88
    path=root/'data'/f'{name}-audit.json';assert sha(path)==expected
    r=json.loads(path.read_text())
    for folder,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(root/folder/(name+suffix))==r[key]
    deps[name]=expected
assert sha(HERE.parent/'87-retained-array-membership/data/RetainedPredicates-support.json')==support['combined_support_sha256']
for folder in ['build','logs','data']:(HERE/folder).mkdir(exist_ok=True)
module='ShapeCache';paths=[str(HERE/'build')]+support['paths']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
if log.exists():log.rename(HERE/'logs'/f'{module}-{time.time_ns()}.log')
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=300)
r=dict(module=module,exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,dependency_receipts=deps,combined_support_sha256=support['combined_support_sha256'])
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(r,indent=2)+'\n')
if p.returncode:print(log.read_text()[-18000:]);raise SystemExit(p.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==3==src.read_text().count('#print axioms')
checked=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    checked.append(dict(theorem=name,axioms=values))
r.update(status='PASS_GENERIC_SHAPE_CACHE',olean_sha256=sha(obj),theorem_audits=checked,scope='Sound reference-shape caching using bounded cache indices and full descriptor equality, preserving original reference guards and all nonreference checks. Equal-length entry/index lists lift compatibility, then combine with explicit count checks. Cache validity remains a quantified hypothesis; no concrete pilot or speedup checked.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(module,'PASS',round(r['seconds'],3),'seconds;',len(checked),'audits',flush=True)
