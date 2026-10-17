"""Positive controls: windows of the 131 bank snakes, the 191-edge witness and the
137-edge alpha=1 counterexample satisfy the local CNF with their true alpha values."""
import json, random
from itertools import combinations
from pysat.solvers import Cadical153
from wincert import Encoding
import os
R=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..')+'/'
snakes=[e['vertex_sequence'] for e in json.load(open(R+'work/bank9.json'))]
for f in ['outputs/square_counterexample.json','outputs/snake9_witness.json']:
    d=json.load(open(R+f)); snakes.append(d.get('vertex_sequence') or d.get('vertices') or d.get('path'))
random.seed(7); out=[]; lo=[]
def alpha(S,c,p,n):
    used={(c^p).bit_length()-1,(c^n).bit_length()-1}
    return sum(c^1<<a^1<<b not in S for a,b in combinations(range(9),2) if a not in used and b not in used)
count={'repeated':0,'distinct':0}
for si,seq in enumerate(snakes):
    S=set(seq)
    idxs=list(range(2,len(seq)-3)); random.shuffle(idxs)
    if si==len(snakes)-2: idxs=[seq.index(0)-2,seq.index(0)-1,seq.index(0)]+idxs[:1]
    for i in idxs[:4]:
        w=seq[i-1:i+4]; ds=[(w[j]^w[j+1]).bit_length()-1 for j in range(4)]
        sh='repeated' if ds[0]==ds[3] else 'distinct'
        perm={}
        for d in ds:
            if d not in perm: perm[d]=len(perm)
        for k in range(9):
            if k not in perm: perm[k]=len(perm)
        tr=lambda v:sum(1<<perm[k] for k in range(9) if (v^w[0])>>k&1)
        W=[tr(v) for v in w]; Sel={tr(v) for v in seq}
        al=[alpha(S,w[j],w[j-1],w[j+1]) for j in (1,2,3)]
        enc=Encoding(W,al,3)
        units=[[enc.var[v] if v in Sel else -enc.var[v]] for v in enc.ball]
        with Cadical153(bootstrap_with=enc.clauses+units) as s: ok=s.solve()
        assert ok,(si,i,al)
        count[sh]+=1; lo.append(min(al))
print('controls passed',count,'min alpha seen',min(lo),'windows with alpha<=3:',sum(x<=3 for x in lo))
json.dump({'scope':'Real snake windows satisfy every clause of the local CNF (with their true alpha values).','controls':count,'all_satisfiable':True,'min_alpha':min(lo)},open(os.path.join(R,'milestones/10-window-aggregate/data/controls.json'),'w'),indent=1)
