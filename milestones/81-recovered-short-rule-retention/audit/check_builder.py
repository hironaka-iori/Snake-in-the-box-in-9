"""Compare the exact builder loop with the normalized forty-rule catalogue."""
from pathlib import Path
import ast,hashlib,json,re,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic();rules=read(HERE/'data/normalized-rules.json')
model_path=ROOT/'milestones/70-proof-supported-share-model/data/enriched-model.json'
extension_path=ROOT/'milestones/59-extended-share-window/extended/data/model.json'
case_paths=[ROOT/'milestones'/name/'data/cases.json' for name in
    ['47-critical-singleton-patterns','48-low-count-compatibility','49-six-direction-pair-catalogue']]
original=read(model_path)['additional_proved_rules']
reconstructed=[]
for path in case_paths:
    reconstructed.extend(dict(row,source=path.parents[1].name) for row in read(path))
reconstructed.append(dict(number=501,source='50-three-count-return',dirs=[0,1,2,3,4,0],
    positions=[1,4,5],kind='sum',cap=12))
assert reconstructed==original,'Current source cases differ from the saved builder inputs'
assert len(rules)==len(original)==40
for a,b in zip(rules,original):
    assert a['number']==b['number'] and a['dirs']==b['dirs'] and a['source']==b['source']
    if a['kind']=='sum':assert a['positions']==b['positions'] and a['cap']==b['cap']
    elif b['source'].startswith('47'):assert a['caps']==[[b['position'],1]]
    else:assert a['caps']==[list(x) for x in zip(b['positions'],b['caps'])]
def parse_list(module,var):
    text=(HERE/'lean'/f'{module}.lean').read_text()
    text=text.split(f'def {var} : List (List Nat × CountTest) := ',1)[1].split('\n\ntheorem',1)[0]
    text=re.sub(r'\.caps (\[[^\]]*\])',r'("caps",\1)',text)
    text=re.sub(r'\.sum (\[[^\]]*\]) (\d+)',r'("sum",\1,\2)',text)
    return ast.literal_eval(text)
caps=parse_list('CapCatalogue','capRules');sums=parse_list('SumCatalogue','sumRules')
assert caps==[(r['dirs'],('caps',[tuple(x) for x in r['caps']])) for r in rules if r['kind']=='caps']
assert sums==[(r['dirs'],('sum',r['positions'],r['cap'])) for r in rules if r['kind']=='sum']
builder=ROOT/'milestones/70-proof-supported-share-model/scripts/build.py'
tree=ast.parse(builder.read_text())
loop=next(n for n in tree.body if isinstance(n,ast.For) and isinstance(n.target,ast.Tuple) and
          [e.id for e in n.target.elts]==['di','ds'])
node=next(n for n in loop.body if isinstance(n,ast.If) and isinstance(n.test,ast.Name) and n.test.id=='enriched')
exact=compile(ast.fix_missing_locations(ast.Module(body=node.body,type_ignores=[])),str(builder),'exec')
def canon(w):
    labels={};return tuple(labels.setdefault(x,len(labels)) for x in w)
codes=np.arange(46656,dtype=np.int32);C=np.stack([codes//6**j%6+1 for j in range(5,-1,-1)],axis=1)
extensions=read(extension_path)['extensions']
assert len(extensions)==505
total_kept=0;matches=0;digest=hashlib.sha256();per_rule={r['number']:0 for r in rules}
for di,ds in enumerate(extensions):
    expected=np.ones(46656,dtype=bool)
    env=dict(np=np,short_rules=original,ds=ds,C=C,keep=expected,canon=canon)
    exec(exact,env)
    actual=np.ones(46656,dtype=bool)
    for r in rules:
        L=len(r['dirs']);positions=r['positions'] if r['kind']=='sum' else [p for p,_ in r['caps']]
        assert all(1<=j<L for j in positions)
        for offset in range(10-L):
            for reverse in [False,True]:
                piece=ds[offset:offset+L]
                if canon(piece[::-1] if reverse else piece)!=tuple(r['dirs']):continue
                points=[offset+(L-j if reverse else j) for j in positions]
                if not all(3<=j<=8 for j in points):continue
                values=[codes//6**(5-(k-3))%6+1 for k in points]
                if r['kind']=='sum':
                    bad=(sum(values)<=r['cap']) & np.logical_and.reduce([v<6 for v in values])
                else:bad=np.logical_and.reduce([v<=cap for v,(_,cap) in zip(values,r['caps'])])
                actual&=~bad;matches+=1;per_rule[r['number']]+=1
    assert np.array_equal(actual,expected),di
    total_kept+=int(actual.sum());digest.update(actual.tobytes())
out=dict(status='PASS_EXACT_RECOVERED_BUILDER_LOOP',direction_shapes=505,codes_per_shape=46656,
    candidate_pairs=505*46656,kept_pairs=total_kept,rejected_pairs=505*46656-total_kept,
    matched_rule_placements=matches,placements_per_rule=per_rule,mask_sha256=digest.hexdigest(),
    reconstructed_source_rules_match=True,
    source_sha256={p.relative_to(ROOT).as_posix():sha(p) for p in [Path(__file__),builder,model_path,
      extension_path,*case_paths,HERE/'data/normalized-rules.json',
      HERE/'lean/CapCatalogue.lean',HERE/'lean/SumCatalogue.lean',HERE/'lean/ShortRetention.lean']},
    seconds=time.monotonic()-start,
    scope='Executes the exact recovered-rule AST from the graph builder for all505*46656 inputs and compares the parsed Lean catalogue conventions. Separate from Lean proof of Python execution; full graph arrays not rebuilt.')
(HERE/'data/builder-comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],out['candidate_pairs'],'pairs;',matches,'rule placements;',round(out['seconds'],2),'seconds')
