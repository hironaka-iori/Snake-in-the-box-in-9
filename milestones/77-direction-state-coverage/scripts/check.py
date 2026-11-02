"""Check one module against the pinned inherited environment."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
OLD=ROOT/'milestones/75-exact-history-bridge/lookup'
receipt=json.loads((OLD/'data/proof-audit.json').read_text())
assert receipt['status']=='PASS_EXACT_GRAPH_SHARE_LOOKUP'
ADAPTER=ROOT/'milestones/73-countfree-share-catalogue/adapter'
support=json.loads((ADAPTER/'data/support.json').read_text())
for row in support['modules']:
    assert sha(ADAPTER/'upstream'/(row['module']+'.lean'))==row['source_sha256']
    assert sha(Path(row['olean_path']))==row['olean_sha256']
SHIFT=ROOT/'milestones/74-graph-interpretation-audit'
shift=json.loads((SHIFT/'data/proof-audit.json').read_text())
assert sha(SHIFT/'lean/WindowStateShift.lean')==shift['source_sha256']
assert sha(SHIFT/'build/WindowStateShift.olean')==shift['olean_sha256']
module=sys.argv[1]
if module.startswith('LookupChunk'):
    deps=['LookupDefinitions']
elif module=='LookupDefinitions':
    deps=['DirectionTables']
elif module=='LookupTableCheck':
    deps=['LookupDefinitions']+[f'LookupChunk{i:02d}' for i in range(6)]
elif module=='CoverageLeaf11':
    deps=['PrunedAssembly']+[f'CoverageTail{i:02d}' for i in range(7)]
elif module.startswith(('CoverageLeaf','CoverageTail')):
    deps=['DirectionTables','PrunedEnumeration']
elif module=='CoverageAssembly':
    deps=['PrunedAssembly']+[p.stem for p in sorted((HERE/'lean').glob('CoverageLeaf*.lean'))]
else:
    deps={'PrunedEnumeration':[],'PrunedAssembly':['PrunedEnumeration'],'DirectionTables':[],'LookupTableCheck':['DirectionTables'],'DirectionCoverage':['DirectionTables','PrunedEnumeration','CoverageAssembly'],'ActualDirectionIds':['DirectionTables','DirectionCoverage'],'HistoryCompatibilityData':['DirectionTables'],'HistoryShape':['DirectionTables','DirectionCoverage','ActualDirectionIds','HistoryCompatibilityData']}[module]
for dep in deps:
    record=json.loads((HERE/'data'/(dep+'-audit.json')).read_text())
    assert record['status']=='PASS_LEAN_MODULE'
    assert sha(HERE/'lean'/(dep+'.lean'))==record['source_sha256']
    assert sha(HERE/'build'/(dep+'.olean'))==record['olean_sha256']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH']
paths=[str(HERE/'build'),str(HERE/'history/build'),str(ROOT/'milestones/75-exact-history-bridge/history/build')]+receipt['paths'];env['LEAN_PATH']=';'.join(paths)
history_receipts=[]
if module in ['ActualDirectionIds','HistoryShape','HistoryCompatibilityData']:
    old_history=ROOT/'milestones/75-exact-history-bridge/history'
    h=json.loads((old_history/'data/proof-audit.json').read_text())
    assert h['status']=='PASS_EXACT_HISTORY'
    for row in h['records']:
        assert sha(old_history/'lean'/(row['module']+'.lean'))==row['source_sha256']
        assert sha(old_history/'build'/(row['module']+'.olean'))==row['olean_sha256']
    history_receipts.append(sha(old_history/'data/proof-audit.json'))
if module in ['ActualDirectionIds','HistoryShape']:
    h=json.loads((HERE/'history/data/proof-audit.json').read_text())
    assert h['status']=='PASS_NUMERIC_HISTORY_AND_SIGNATURE_EQUIVALENCE'
    assert sha(HERE/'history/lean/NumericHistory.lean')==h['source_sha256']
    assert sha(HERE/'history/build/NumericHistory.olean')==h['olean_sha256']
    history_receipts.append(sha(HERE/'history/data/proof-audit.json'))
src=HERE/'lean'/(module+'.lean');obj=HERE/'build'/(module+'.olean');log=HERE/'logs'/(module+'.log')
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    proc=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
record=dict(module=module,exit_code=proc.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,inherited_support_sha256=sha(ADAPTER/'data/support.json'),shift_receipt_sha256=sha(SHIFT/'data/proof-audit.json'),history_receipts=history_receipts,dependencies={dep:sha(HERE/'data'/(dep+'-audit.json')) for dep in deps})
(HERE/'logs'/(module+'-record.json')).write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
if proc.returncode:print(log.read_text()[-6000:]);raise SystemExit(proc.returncode)
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
record.update(status='PASS_LEAN_MODULE',olean_sha256=sha(obj),theorem_audits=audits,scope='Direction-table or actual-snake interface only. No complete exclusion/credit lookup or full potential proof; inherited objects reused with hashes.')
(HERE/'data'/(module+'-audit.json')).write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(module,'PASS',record['seconds'],'seconds;',len(audits),'axiom audits',flush=True)
