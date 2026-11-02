"""Check generic batch membership from previously checked witness lookups."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1]
REPO=HERE.parents[1]
P90=HERE.parent/'90-context-witness-certificates'
P89=HERE.parent/'89-shared-cover-certification'
P88=HERE.parent/'88-retention-diagram-certificate'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
deps={}
def verify(root,name,pin=None):
    path=root/'data'/f'{name}-audit.json'
    if pin:assert sha(path)==pin
    r=json.loads(path.read_text());assert r['status'].startswith('PASS_')
    for folder,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(root/folder/(name+suffix))==r[key]
    deps[name]=sha(path)
    return r
tables=verify(P90,'WitnessTablesChecks','1ef0a67b7a0fde9a34deb0eecf17b90783b1fc519d60b5cb9cc78b277370ac93')
data=verify(P90,'WitnessTablesData','4b1fadf7fbe5390f1decfa7c865c17afac63556190418d5e6804bc92f56d3d78')
support=verify(P90,'WitnessLookup','b6e78a765bcfafb3f86b8bf0c45ee87a72efa8c706c2e595728449d8881bd8bb')
verify(P89,'BalancedLookup','14c9cfabd213629b7ea03aa57f49400211f14c51299e6d9ecf509853c9f5e4ff')
for name,expected in support['dependency_receipts'].items():
    root=P89 if name in ['SharedAssembly','ContextTransport'] else P88
    verify(root,name,expected)
for r in [tables,data]:
    for rel,expected in r['dependencies'].items():assert sha(REPO/rel)==expected
assert sha(HERE.parent/'87-retained-array-membership/data/RetainedPredicates-support.json')==support['combined_support_sha256']
for folder in ['build','logs','data']:(HERE/folder).mkdir(exist_ok=True)
module='BatchAssembly';paths=[str(HERE/'build')]+support['paths']
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
assert len(audits)==4==src.read_text().count('#print axioms')
checked=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    checked.append(dict(theorem=name,axioms=values))
r.update(status='PASS_GENERIC_BATCH_ASSEMBLY',olean_sha256=sha(obj),theorem_audits=checked,scope='Generic job extraction, bounded-history diagram membership and ordered history-head restoration using the checked direction/reference lookups. Every concrete job-validity, full coverage, numeric-retention and restored-head premise remains explicit. No new concrete class, full batch or snake bound checked.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(module,'PASS',round(r['seconds'],3),'seconds;',len(checked),'audits',flush=True)
