"""Check the generic reference-catalogue interface and exact inherited support."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/79-retained-edge-guards'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
summary=json.loads((OLD/'data/proof-summary.json').read_text())
assert summary['status']=='PASS_ENCODED_GUARDS_AND_TEN_INTERVAL_RETENTION'
for row in summary['receipts']:
    p=OLD/row['receipt'];assert sha(p)==row['sha256'];r=json.loads(p.read_text())
    for sub,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(OLD/sub/(row['module']+suffix))==r[key]
key_modules={}
for name in ['LocalWindowDirKeys6K235','LocalWindowDirKeysR4']:
    src=HERE/'lean'/f'{name}.lean';up=HERE/'upstream'/f'{name}.lean';obj=HERE/'build'/f'{name}.olean'
    assert sha(src)==sha(up)
    receipt=HERE/'data'/f'{name}-audit.json';compiled=json.loads(receipt.read_text())
    assert compiled['status']=='PASS_LEAN_MODULE'
    assert sha(src)==compiled['source_sha256'] and sha(obj)==compiled['olean_sha256']
    assert sha(HERE/'logs'/f'{name}.log')==compiled['log_sha256']
    key_modules[name]=dict(source_sha256=sha(src),object_sha256=sha(obj),upstream_sha256=sha(up),receipt_sha256=sha(receipt))
for folder in ['build','data','logs']:(HERE/folder).mkdir(exist_ok=True)
module='ReferenceInterface'
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
old=json.loads((OLD/'data/IntervalGuards-audit.json').read_text())
paths=[str(HERE/'build')]+old['paths']
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=240)
r=dict(module=module,exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,
    inherited_summary_sha256=sha(OLD/'data/proof-summary.json'),key_modules=key_modules,
    dependencies={'ReferenceRetention':sha(OLD/'data/ReferenceRetention-audit.json')})
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(r,indent=2)+'\n')
if p.returncode:print(log.read_text()[-16000:]);raise SystemExit(p.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
rows += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(rows)==src.read_text().count('#print axioms')
audits=[]
for name,axs in rows:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    audits.append(dict(theorem=name,axioms=values))
r.update(status='PASS_LEAN_MODULE',olean_sha256=sha(obj),theorem_audits=audits,
    scope='Generic reference-catalogue coverage and actual-snake guard retention. AllRefuted6K235 and AllRefuted236 remain explicit premises. Exact union coverage and closed contributor certificates are separate. Hash-matched inherited objects reused; full closure not rebuilt.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(module,'PASS',round(r['seconds'],3),'seconds;',len(audits),'audits',flush=True)
