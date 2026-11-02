"""Check generic literal-tree lookup with the lightweight milestone88 environment."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1]
OLD=HERE.parent/'88-retention-diagram-certificate'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
deps={}
pins={'Boxes':('source_sha256','4cfdc5590fd95109d68ae36a516f97d0b767c16854fd43396eecc91998c2cc55'),
      'CoverTree':('source_sha256','a965f33fb9cbfa4cde96f4dd4f121ecf356f3e055fbd3cb6d314fd732b18c779')}
for name,(field,pin) in pins.items():
    path=OLD/'data'/f'{name}-audit.json';r=json.loads(path.read_text())
    assert r['status'] in ['PASS_GENERIC_COVER_MODULE','PASS_LEAN_MODULE'] and r[field]==pin
    for folder,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(OLD/folder/(name+suffix))==r[key]
    deps[name]=sha(path)
assert json.loads((OLD/'data/CoverTree-audit.json').read_text())['dependencies']['Boxes']==deps['Boxes']
module='BalancedLookup';paths=[str(HERE/'build'),str(OLD/'build')]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
if log.exists():log.rename(HERE/'logs'/f'{module}-{time.time_ns()}.log')
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=240)
r=dict(module=module,exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,dependency_receipts=deps)
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(r,indent=2)+'\n')
if p.returncode:print(log.read_text()[-16000:]);raise SystemExit(p.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==5==src.read_text().count('#print axioms')
checked=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    checked.append(dict(theorem=name,axioms=values))
r.update(status='PASS_GENERIC_BALANCED_LOOKUP',olean_sha256=sha(obj),theorem_audits=checked,scope='Generic checked split-size tree lookup equals flattened-list getD for every index and supplied default. A checked flatten equality transfers lookup to an original list. Tree balance, concrete table certificates and performance improvements are not established by this module.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(module,'PASS',round(r['seconds'],3),'seconds;',len(checked),'audits',flush=True)
