"""Check short-rule transfer using exact milestone79 support."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/79-retained-edge-guards'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
summary=json.loads((OLD/'data/proof-summary.json').read_text())
assert summary['status']=='PASS_ENCODED_GUARDS_AND_TEN_INTERVAL_RETENTION'
for row in summary['receipts']:
    p=OLD/row['receipt'];assert sha(p)==row['sha256'];r=json.loads(p.read_text())
    for sub,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(OLD/sub/(row['module']+suffix))==r[key]
for folder in ['build','data','logs']:(HERE/folder).mkdir(exist_ok=True)
module=sys.argv[1]
deps={'PositionTransfer':[],'GuardTransfer':['PositionTransfer'],'JointCountBridge':[],'JointCountTags':[],
    'MultiCentreCount':['JointCountTags'],
    'CapCatalogue':['GuardTransfer'],'SumCatalogue':['GuardTransfer','JointCountBridge','JointCountTags','MultiCentreCount'],
    'ShortRetention':['CapCatalogue','SumCatalogue']}[module]
for dep in deps:
    r=json.loads((HERE/'data'/f'{dep}-audit.json').read_text());assert r['status']=='PASS_LEAN_MODULE'
    assert sha(HERE/'lean'/f'{dep}.lean')==r['source_sha256']
    assert sha(HERE/'build'/f'{dep}.olean')==r['olean_sha256']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
old=json.loads((OLD/'data/IntervalGuards-audit.json').read_text())
paths=[str(HERE/'build')]+old['paths']
if module in ['CapCatalogue','SumCatalogue','ShortRetention']:
    support=json.loads((HERE/'data/short-support.json').read_text())
    for row in support['modules'].values():
        assert sha(Path(row['source']))==row['source_sha256']
        assert sha(Path(row['object']))==row['object_sha256']
    paths.insert(1,support['overlay']);paths.extend(support['extra_paths'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=240)
r=dict(module=module,exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,
    inherited_summary_sha256=sha(OLD/'data/proof-summary.json'),dependencies={dep:sha(HERE/'data'/f'{dep}-audit.json') for dep in deps})
if module in ['CapCatalogue','SumCatalogue','ShortRetention']:r['short_support_sha256']=sha(HERE/'data/short-support.json')
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(r,indent=2)+'\n')
if p.returncode:print(log.read_text()[-12000:]);raise SystemExit(p.returncode)
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
    scope='Short-rule guard transfer and stated instantiations only. No full retained-array, credit or potential theorem. Hash-matched support reused.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(module,'PASS',round(r['seconds'],3),'seconds;',len(audits),'audits',flush=True)
