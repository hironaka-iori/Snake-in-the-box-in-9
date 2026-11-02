"""Build a concrete direction-zero certificate from pinned rejection boxes."""
from pathlib import Path
import gzip,hashlib,json,time
HERE=Path(__file__).resolve().parents[1];OLD=HERE.parent/'87-retained-array-membership'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();start=time.monotonic()
bp=HERE/'data/box-cover-selected-max-gain.json.gz';gp=OLD/'data/coverage-membership-dag.json.gz'
b=json.loads(gzip.decompress(bp.read_bytes()));g=json.loads(gzip.decompress(gp.read_bytes()))
case=b['directions'][0];assert case['direction']==0
entries=[(b['box_catalogue'][r['box']],r['witness']) for r in case['selected']]
assert all(len(box)==6 and all(1<=lo<=hi<=6 for lo,hi in box) for box,w in entries)
root=g['roots'][case['dag_set']];diagram=g['nodes']
trees=[];ids={};calls=0
def intern(key):
    if key not in ids:ids[key]=len(trees);trees.append(key)
    return ids[key]
def step(node,x):return node if node<2 else diagram[node-2][x]
def build(pref,node,candidates):
    global calls
    calls+=1;depth=len(pref)
    if node==1:return intern(('accept',))
    for i in candidates:
        if all(lo==1 and hi==6 for lo,hi in entries[i][0][depth:]):
            assert all(lo<=x<=hi for x,(lo,hi) in zip(pref,entries[i][0]))
            return intern(('reject',i))
    assert depth<6,dict(pref=pref,node=node,candidates=candidates)
    children=tuple(build(pref+[x],step(node,x),[i for i in candidates if entries[i][0][depth][0]<=x<=entries[i][0][depth][1]]) for x in range(1,7))
    return intern(('split',*children))
tree=build([],root,list(range(len(entries))))
# Pointwise independent replay of the generated certificate on all six-digit codes.
accepted=0
for code in range(46656):
    symbols=[code//6**j%6+1 for j in range(5,-1,-1)]
    ci=tree;node=root;depth=0
    while trees[ci][0]=='split':
        ci=trees[ci][symbols[depth]];node=step(node,symbols[depth]);depth+=1
    if trees[ci][0]=='accept':
        assert node==1;accepted+=1
    else:
        box=entries[trees[ci][1]][0];assert all(lo<=x<=hi for x,(lo,hi) in zip(symbols,box))
assert accepted==case['accepted_count']
lean=HERE/'lean';lean.mkdir(exist_ok=True)
array=lambda xs:'#['+','.join(map(str,xs))+']'
graph='import CoverTree\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace Snake9.Certificate88\nopen Snake9.Boxes88\n\ndef retainedDiagram : Diagram := #[\n'+',\n'.join(array(row) for row in diagram)+'\n]\n\nend Snake9.Certificate88\n'
(lean/'GraphData.lean').write_text(graph,encoding='utf-8')
def witness(w):
    family=w['family'];i=w['index']
    if family=='history':return f'Witness.history {i}'
    return f'Witness.{family} {i} {w["offset"]} '+('true' if w['reverse'] else 'false')
data='import GraphData\nimport BoxWitness\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace Snake9.Certificate88\nopen Snake9.Boxes88\n\n'
data+='def entries000 : List (Box × Witness) := [\n'+',\n'.join('(['+','.join(f'({lo},{hi})' for lo,hi in box)+'], '+witness(w)+')' for box,w in entries)+'\n]\n'
data+='def boxes000 : List Box := entries000.map Prod.fst\n'
data+=f'def root000 : Nat := {root}\n'
for i,item in enumerate(trees):
    if item[0]=='accept':value='CoverTree.accept'
    elif item[0]=='reject':value=f'CoverTree.reject {item[1]}'
    else:value='CoverTree.split ['+','.join(f'tree000_{j}' for j in item[1:])+']'
    data+=f'def tree000_{i} : CoverTree := {value}\n'
data+=f'def tree000 : CoverTree := tree000_{tree}\n\nend Snake9.Certificate88\n'
(lean/'Case000Data.lean').write_text(data,encoding='utf-8')
payload=dict(direction=0,history=0,root=root,entries=entries,trees=trees,tree=tree,
    input_sha256={bp.name:sha(bp),str(gp.relative_to(HERE.parents[1])):sha(gp)})
packed=gzip.compress(json.dumps(payload,separators=(',',':')).encode(),mtime=0)
(HERE/'data/pilot000-certificate.json.gz').write_bytes(packed)
report=dict(status='GENERATED_PILOT_KERNEL_CHECK_PENDING',direction=0,history=0,boxes=len(entries),root=root,unique_tree_nodes=len(trees),expanded_node_visits=calls,
    pointwise_checks=46656,accepted_codes=accepted,source_sha256={n:sha(lean/n) for n in ['GraphData.lean','Case000Data.lean']},
    input_sha256=payload['input_sha256'],certificate_sha256=hashlib.sha256(packed).hexdigest(),script_sha256=sha(Path(__file__)),seconds=time.monotonic()-start,
    scope='Concrete proof data and complete Python pointwise replay; Lean witness validation and coverage reduction still required.')
(HERE/'data/pilot000-generation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
