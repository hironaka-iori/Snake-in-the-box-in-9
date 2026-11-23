from collections import Counter,defaultdict
from itertools import product
from pathlib import Path
import json,sys,subprocess
D=Path(__file__).resolve().parent;R=D.parent
sys.path.insert(0,str(R/'q9_internal_xor_20261121'))
from verify import quadratic,wfrom,canon
def checked(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p)
    assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:])) and not quadratic(p)
def read(name):
    return [s.split() for s in (D/name).read_text().splitlines()]
ref={i:{canon(w) for w in (R/'q9_gap_generations'/f'prior{i}.words').read_text().split()} for i in (189,190,191)}
runs={}; allpaths=defaultdict(set);tot=0
for name in ('mixed','extra','archive'):
    rows=read(name+'.log')
    end,=[t for t in rows if t[0]=='DONE']
    epochs,steps,topology,forest,distinct,disconnected,bcomp,bscore=map(int,end[1:])
    moves=[list(map(int,t[1:])) for t in rows if t[0]=='MOVE']
    assert sum(p for _,p,a in moves)==epochs*steps
    if name!='archive':assert [t for t in read(name+'_replay.log') if t[0]!='SET']==rows
    tot+=epochs*steps
    for t in rows:
        if t[0]!='PATH':continue
        p=list(map(int,t[2:]));checked(p);assert len(p)==int(t[1])+1;allpaths[len(p)-1].add(wfrom(p))
    runs[name]=dict(proposals=epochs*steps,accepted_forest_visits=forest,distinct_forests=distinct,accepted_disconnected=disconnected,moves=moves,best_component_edges=bcomp,best_score=bscore)
ctrl=[]
for name in ('control','join_control'):
    paths=[list(map(int,t[2:])) for t in read(name+'.log') if t[0]=='PATH' and t[1]=='191'];assert paths
    for p in paths:checked(p)
    ctrl.append({'control':name,'classes':len({wfrom(p) for p in paths})})
pairs={tuple(t) for t in read('forest.words')};arms=defaultdict(lambda:[set(),set()])
for a,b in pairs:
    size=lambda x:len(x)+1 if x!='-' else 1
    assert size(a)+size(b)==193
    pools=arms[size(b)];pools[0].add(a);pools[1].add(b)
mixed=sorted({pair for left,right in arms.values() for pair in product(left,right)})
(D/'forest_cross.words').write_text(''.join(' '.join(t)+'\n' for t in mixed))
with (D/'forest_cross.words').open() as inp,(D/'joins_cross.log').open('w') as out:
    subprocess.run(['/tmp/q9_occupancy_join21','5000000'],stdin=inp,stdout=out,check=True)
join=read('joins_cross.log')
for t in join:
    if t[0]=='PATH':
        p=list(map(int,t[2:]));checked(p);assert len(p)==193
print(json.dumps(dict(target_proposals_excluding_replay=tot,runs=runs,emitted_classes={n:{'count':len(v),'outside_local_reference':len(v-ref.get(n,set()))} for n,v in allpaths.items()},control=ctrl,original_shape_pairs=len(pairs),cross_shape_pairs=len(mixed),cross_result=join),indent=2))
