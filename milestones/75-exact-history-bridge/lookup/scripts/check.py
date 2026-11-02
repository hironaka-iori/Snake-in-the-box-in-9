"""Check exact graph share lookup against hash-matched inherited support."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
ADAPTER=ROOT/'milestones/73-countfree-share-catalogue/adapter'
SHIFT=ROOT/'milestones/74-graph-interpretation-audit'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
support=read(ADAPTER/'data/support.json');audit=read(ADAPTER/'data/proof-audit.json')
assert audit['status']=='PASS_CONDITIONAL_CATALOGUE_DISPATCH'
assert sha(ADAPTER/'data/support.json')==audit['support_record_sha256']
for row in support['modules']:
    assert sha(ADAPTER/'upstream'/(row['module']+'.lean'))==row['source_sha256']
    assert sha(Path(row['olean_path']))==row['olean_sha256']
records=read(ADAPTER/'logs/build-record.json')
for row in records:
    assert row['exit_code']==0
    assert sha(ADAPTER/'lean'/(row['module']+'.lean'))==row['source_sha256']
    assert sha(ADAPTER/'build'/(row['module']+'.olean'))==row['olean_sha256']
shift=read(SHIFT/'data/proof-audit.json');assert shift['status']=='PASS_WINDOW_STATE_SHIFT'
assert sha(SHIFT/'lean/WindowStateShift.lean')==shift['source_sha256']
assert sha(SHIFT/'build/WindowStateShift.olean')==shift['olean_sha256']
for name in ['build','logs','data']:(HERE/name).mkdir(parents=True,exist_ok=True)
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH']
paths=[str(HERE/'build'),str(SHIFT/'build')]+records[-1]['paths'];env['LEAN_PATH']=';'.join(paths)
source=HERE/'lean/GraphShareLookup.lean';dest=HERE/'build/GraphShareLookup.olean';log=HERE/'logs/GraphShareLookup.log'
t=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    run=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(dest.with_suffix('.fresh.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=180)
record=dict(exit_code=run.returncode,seconds=time.monotonic()-t,source_sha256=sha(source),paths=paths)
(HERE/'logs/build-record.json').write_text(json.dumps(record,indent=2)+'\n')
if run.returncode:print(log.read_text());raise SystemExit(run.returncode)
os.replace(dest.with_suffix('.fresh.olean'),dest)
text=log.read_text();assert 'sorryAx' not in text and 'error:' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text())
rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
rows += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(rows)==8
checks=[]
for name,values in rows:
    axioms=re.findall(r'[A-Za-z][\w.]*',values)
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
    checks.append(dict(theorem=name,axioms=axioms))
record.update(status='PASS_EXACT_GRAPH_SHARE_LOOKUP',olean_sha256=sha(dest),log_sha256=sha(log),
    adapter_receipt_sha256=sha(ADAPTER/'data/proof-audit.json'),shift_receipt_sha256=sha(SHIFT/'data/proof-audit.json'),
    theorem_audits=checks,scope='Exact orientation selection and actual-snake suffix centres. The share inequality retains all nine local certificate premises. Numeric graph edge membership, history/exclusion dispatch and global potential replay are separate; inherited dependencies were hash checked, not fully rebuilt.')
(HERE/'data/proof-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],record['seconds'],'seconds;',len(checks),'axiom audits')
