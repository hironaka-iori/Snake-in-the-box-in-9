"""Compare the actual history-filter loop with the three Lean rule literals."""
from pathlib import Path
import ast,hashlib,json,re,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
builder=ROOT/'milestones/70-proof-supported-share-model/scripts/build.py'
model=ROOT/'milestones/70-proof-supported-share-model/data/enriched-model.json';md=read(model)
realizations=HERE/'data/realizations.json';rows=read(realizations)['rows']
tree=ast.parse(builder.read_text());loops=[n for n in ast.walk(tree) if isinstance(n,ast.For) and isinstance(n.target,ast.Name) and n.target.id=='pat']
assert len(loops)==1
loop=compile(ast.fix_missing_locations(ast.Module(body=loops,type_ignores=[])),str(builder),'exec')
source=HERE/'lean/HistoryRealizations.lean';text=source.read_text()
sigs=[ast.literal_eval(re.search(rf'def signature{i} : List Nat := (\[[^\n]+\])',text).group(1)) for i in range(3)]
assert sigs==[r['signature'] for r in rows]
rules=HERE/'lean/HistoryExclusions.lean';ruletext=rules.read_text()
assert '[(signature0,5),(signature1,3),(signature2,5)]' in ruletext
assert 'hist.drop (hist.length-3) = rule.1 ∧ digit code rule.2 ≤ 2' in ruletext
assert [(r['signature'],r['caps']) for r in rows]==[(sigs[0],{'5':2}),(sigs[1],{'3':2}),(sigs[2],{'5':2})]
prefix_source=ROOT/'milestones/75-exact-history-bridge/history/lean/ExactHistory.lean'
pt=prefix_source.read_text();literal=re.search(r'def prefixes :[^\n]+:= (\[[\s\S]*?^\])',pt,re.M).group(1)
prefixes=ast.literal_eval(literal);assert prefixes==md['prefixes'] and len(prefixes)==75
table_source=ROOT/'milestones/77-direction-state-coverage/lean/DirectionTables.lean';dt=table_source.read_text()
literal=re.search(r'def extensions :[^\n]+:= (\[[\s\S]*?^\])',dt,re.M).group(1)
extensions=ast.literal_eval(literal)
direction_model=ROOT/'milestones/59-extended-share-window/extended/data/model.json'
assert extensions==read(direction_model)['extensions'] and len(extensions)==505
def actual(hist,cs):
    env=dict(md=md,hist=tuple(hist),cs=cs,c=np.arange(len(cs)),lower=np.zeros(len(cs),dtype=np.int64),
      accept=np.ones(len(cs),dtype=bool),np=np)
    exec(loop,env)
    return env['accept']
def expected(hist,cs):
    return np.logical_and.reduce([~((len(hist)>=3 and list(hist[-3:])==sig)&(cs[:,j]<=2))
      for sig,j in zip(sigs,[5,3,5])])
small=np.repeat(np.arange(1,7)[:,None],6,axis=1);active=[];pairs=0
for q,prefix in enumerate(prefixes):
    for di in range(505):
        hist=prefix+[di];assert np.array_equal(actual(hist,small),expected(hist,small));pairs+=1
        if len(hist)>=3 and hist[-3:] in sigs:active.append((q,di))
assert active==[(43,177),(68,180),(70,177)]
code=np.arange(6**6);C=np.stack([code//6**j%6+1 for j in range(5,-1,-1)],axis=1)
results=[]
for q,di in active:
    mask=actual(prefixes[q]+[di],C);assert np.array_equal(mask,expected(prefixes[q]+[di],C))
    assert int((~mask).sum())==15552
    results.append(dict(history=q,direction=di,accepted=int(mask.sum()),rejected=int((~mask).sum()),
      mask_sha256=hashlib.sha256(mask.tobytes()).hexdigest()))
inputs=[Path(__file__).resolve(),builder,model,realizations,source,rules,prefix_source,table_source,direction_model]
out=dict(status='PASS_EXACT_THREE_HISTORY_FILTER_COMPARISON',history_direction_pairs=pairs,
    uniform_count_tests=pairs*6,active_count_code_tests=len(active)*6**6,active_rules=results,
    inputs={p.relative_to(ROOT).as_posix():sha(p) for p in inputs},
    scope='Exact isolated builder loop, before source-compatibility and other graph filters. Counts are not numbers of newly removed edges from the full retained graph. Python comparison is separate from the Lean theorem.')
(HERE/'data/filter-comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],pairs,'history/direction pairs;',out['active_count_code_tests'],'full count-code tests')
