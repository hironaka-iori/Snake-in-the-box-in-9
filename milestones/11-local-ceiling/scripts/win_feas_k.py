import json, sys, collections
sys.path.insert(0, '/Users/yichenzhan/Downloads/Snake-in-the-box-in-9-main/upstream/milestones/10-window-aggregate/scripts')
import wincert
d=json.load(open(sys.argv[1])); S=set(d['S']); radius=int(sys.argv[2]); ks=[int(k) for k in sys.argv[3:]]
import itertools
pairs=list(itertools.combinations(range(9),2))
alpha={x:sum(1 for i,j in pairs if not({x^1<<i,x^1<<j,x^1<<i^1<<j}&S)) for x in S}
def canon(ds):
    m={}; return tuple(m.setdefault(x,len(m)) for x in ds)
wins=collections.Counter()
for c in d['cycles']:
    L=len(c)
    for k in ks:
        for st in range(L):
            vs=[c[(st+i)%L] for i in range(k+2)]
            ds=[(vs[i]^vs[i+1]).bit_length()-1 for i in range(k+1)]
            wins[(canon(ds),tuple(alpha[x] for x in vs[1:-1]))]+=1
ok=True
for (ds,cs),n in sorted(wins.items()):
    enc=wincert.Encoding(wincert.window_from_dirs(list(ds)), list(cs), radius)  # exact counts
    st,_,cuts=wincert.decide(enc, certify=False)
    ok &= st=='SAT'; print(len(cs), ds, cs, n, st, cuts, flush=True)
print("radius",radius,"ks",ks,"all feasible:", ok)
