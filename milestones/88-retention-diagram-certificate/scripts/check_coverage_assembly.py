"""Check the generic assembly of witness exclusion and diagram coverage."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
deps={}
for name,status,pin in [
    ('BoxWitness','PASS_LEAN_MODULE','ff5b4d7546edd5a22dacea3ca180e0e906710c0122f6a470a35b278c546f3001'),
    ('CoverTree','PASS_GENERIC_COVER_MODULE',None)]:
    p=HERE/'data'/f'{name}-audit.json';r=json.loads(p.read_text())
    assert r['status']==status
    if pin:assert sha(p)==pin
    for folder,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(HERE/folder/(name+suffix))==r[key]
    deps[name]=sha(p)
    if name=='BoxWitness':support=r
assert json.loads((HERE/'data/CoverTree-audit.json').read_text())['source_sha256']=='a965f33fb9cbfa4cde96f4dd4f121ecf356f3e055fbd3cb6d314fd732b18c779'
old=HERE.parent/'87-retained-array-membership'
assert sha(old/'data/RetainedPredicates-support.json')==support['combined_support_sha256']
paths=support['paths'];module='CoverageAssembly'
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
if log.exists():log.rename(HERE/'logs'/f'{module}-{time.time_ns()}.log')
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=300)
r=dict(module=module,exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,dependency_receipts=deps,combined_support_sha256=support['combined_support_sha256'])
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(r,indent=2)+'\n')
if p.returncode:print(log.read_text()[-22000:]);raise SystemExit(p.returncode)
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
r.update(status='PASS_GENERIC_COVERAGE_ASSEMBLY',olean_sha256=sha(obj),theorem_audits=checked,scope='Generic implication from numeric acceptance, concrete witness validity and concrete coverage checks to diagram membership. Actual-snake specialization keeps both reference-catalogue premises explicit. No particular diagram or finite witness list is certified by this module.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(module,'PASS',round(r['seconds'],3),'seconds;',len(checked),'audits',flush=True)
