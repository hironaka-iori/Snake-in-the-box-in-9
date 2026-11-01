"""Check only the small state-shift identities with pinned compiled support."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/73-countfree-share-catalogue/adapter'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt=OLD/'data/proof-audit.json';audit=json.loads(receipt.read_text())
assert audit['status']=='PASS_CONDITIONAL_CATALOGUE_DISPATCH'
support=OLD/'data/support.json';assert sha(support)==audit['support_record_sha256']
records=json.loads((OLD/'logs/build-record.json').read_text())
base=records[0];assert base['module']=='CanonicalShareAdapter' and base['exit_code']==0
assert sha(OLD/'lean/CanonicalShareAdapter.lean')==base['source_sha256']
assert sha(OLD/'build/CanonicalShareAdapter.olean')==base['olean_sha256']
for item in json.loads(support.read_text())['modules']:
    assert sha(OLD/'upstream'/(item['module']+'.lean'))==item['source_sha256']
    assert sha(Path(item['olean_path']))==item['olean_sha256']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
for d in ['build','logs','data']:(HERE/d).mkdir(exist_ok=True)
paths=[str(HERE/'build'),str(OLD/'build')]+base['paths']
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
module=sys.argv[1] if len(sys.argv)>1 else 'WindowStateShift'
assert module in ['WindowStateShift','PotentialRangeObstruction']
source=HERE/'lean'/(module+'.lean');dest=HERE/'build'/(module+'.olean');log=HERE/'logs'/(module+'.log');t=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    run=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(dest.with_suffix('.fresh.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=120)
record=dict(exit_code=run.returncode,seconds=time.monotonic()-t,source_sha256=sha(source),support_receipt_sha256=sha(receipt),support_record_sha256=sha(support),support_object_sha256=base['olean_sha256'])
(HERE/'logs'/(module+'-build-record.json')).write_text(json.dumps(record,indent=2)+'\n')
if run.returncode:print(log.read_text());raise SystemExit(run.returncode)
os.replace(dest.with_suffix('.fresh.olean'),dest)
txt=log.read_text();assert all(s not in txt for s in ['error:','sorryAx','failed to delete'])
assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text())
rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",txt,re.S);assert len(rows)==(4 if module=='WindowStateShift' else 1)
checks=[]
for name,axs in rows:
    axioms=re.findall(r'[A-Za-z][\w.]*',axs);assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
    checks.append(dict(theorem=name,axioms=axioms))
record.update(status='PASS_WINDOW_STATE_SHIFT' if module=='WindowStateShift' else 'PASS_POTENTIAL_RANGE_OBSTRUCTION',olean_sha256=sha(dest),log_sha256=sha(log),theorem_audits=checks,scope='Fresh small-module check with previously source/audit-matched support environment. No contributor UpperBound234 or full graph build; no state membership, history automaton, credit table, potential replay or numerical upper bound. The obstruction lemma is conditional algebra and supplies no graph path.')
(HERE/'data'/('proof-audit.json' if module=='WindowStateShift' else 'potential-obstruction-proof.json')).write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],record['seconds'],'seconds;',len(checks),'axiom audits.')
