"""Check the history exclusion bridge with pinned, reused support."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();read=lambda p:json.loads(p.read_text())
OLD=ROOT/'milestones/79-retained-edge-guards';summary=read(OLD/'data/proof-summary.json')
assert summary['status']=='PASS_ENCODED_GUARDS_AND_TEN_INTERVAL_RETENTION'
for row in summary['receipts']:
    receipt=OLD/row['receipt'];assert sha(receipt)==row['sha256'];r=read(receipt)
    for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(OLD/folder/(row['module']+ext))==r[key]
module=sys.argv[1]
deps={'HistoryRealizations':[],'HistoryUnique':['HistoryRealizations','HistoryWindow'],
      'HistoryCountSupport':[],
      'TerminalCount':['HistoryCountSupport'],'CountPhase04':['HistoryCountSupport'],'CountPhase29':['HistoryCountSupport'],
      'HistoryExclusions':['HistoryUnique','TerminalCount','CountPhase04','CountPhase29']}[module]
for dep in deps:
    r=read(HERE/'data'/f'{dep}-audit.json');assert r['status']=='PASS_LEAN_MODULE'
    assert sha(HERE/'lean'/f'{dep}.lean')==r['source_sha256']
    assert sha(HERE/'build'/f'{dep}.olean')==r['olean_sha256']
    assert sha(HERE/'logs'/f'{dep}.log')==r['log_sha256']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
paths=[str(HERE/'build')]+read(OLD/'data/IntervalGuards-audit.json')['paths']
if module=='HistoryExclusions':
    oldpos=ROOT/'milestones/81-recovered-short-rule-retention'
    pos=read(oldpos/'data/PositionTransfer-audit.json');assert pos['status']=='PASS_LEAN_MODULE'
    for sub,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(oldpos/sub/('PositionTransfer'+ext))==pos[key]
    paths.append(str(oldpos/'build'))
if module in ['HistoryCountSupport','TerminalCount','CountPhase04','CountPhase29','HistoryExclusions']:
    comp=read(HERE/'data/compatible-count-sources.json')
    for rel,digest in comp['source_sha256'].items():assert sha(ROOT/rel)==digest
    assert sha(HERE/'lean/HistoryCountSupport.lean')==comp['support_source_sha256']
    for name,row in comp['roots'].items():
        assert sha(ROOT/row['source'])==row['source_sha256']
        assert sha(HERE/'lean'/(name+'.lean'))==row['adapted_source_sha256']
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),
      '-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,
      stdout=out,stderr=subprocess.STDOUT,timeout=240)
r=dict(module=module,exit_code=result.returncode,seconds=time.monotonic()-start,
    source_sha256=sha(src),log_sha256=sha(log),paths=paths,inherited_summary_sha256=sha(OLD/'data/proof-summary.json'),
    dependencies={dep:sha(HERE/'data'/f'{dep}-audit.json') for dep in deps})
if module in ['HistoryCountSupport','TerminalCount','CountPhase04','CountPhase29','HistoryExclusions']:
    r['compatible_count_sources_sha256']=sha(HERE/'data/compatible-count-sources.json')
if module=='HistoryExclusions':r['position_support_receipt_sha256']=sha(oldpos/'data/PositionTransfer-audit.json')
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(r,indent=2)+'\n')
if result.returncode:print(log.read_text()[-12000:]);raise SystemExit(result.returncode)
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
    scope='Three history exclusions and stated transport only; no full retained-array, credit or potential theorem. Pinned support reused.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(module,'PASS',round(r['seconds'],3),'seconds;',len(audits),'audits',flush=True)
