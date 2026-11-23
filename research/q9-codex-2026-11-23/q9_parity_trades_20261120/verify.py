"""Recheck the surviving 96-point sets by direct longest-path DFS, independently of C++ edge branching."""
from pathlib import Path
from collections import Counter
import json
root = Path(__file__).resolve().parent
refs = (root.parent / 'q9_reordered_segments_20261120/reference191.words').read_text().split()

def norm(w):
    labels = {}
    return ''.join(str(labels.setdefault(x,len(labels))) for x in w)
def canonical(w):
    return min(norm(w),norm(w[::-1]))

def witness(file):
    found, source = (root/file).read_text().splitlines()
    path = list(map(int,found.split()[1:]))
    assert len(path)==len(set(path))==192
    assert all(0<=x<512 for x in path)
    assert all(((path[i]^v).bit_count()==1)==(j==i+1) for j,v in enumerate(path) for i in range(j))
    _,r,_,side,_,t,_,c,_,swaps=source.split()
    r,side,t,c,swaps=map(int,(r,side,t,c,swaps))
    pts=[0]
    for bit in refs[r]:
        pts.append(pts[-1]^(1<<int(bit)))
    fixed={v^side for v in pts[side::2]}
    transformed={v^t if min((v^c).bit_count(),(v^c^t).bit_count())<=2 else v for v in fixed}
    assert len(fixed-transformed)==swaps and transformed=={v for v in path if not v.bit_count()%2}
    word=canonical(''.join(str((a^b).bit_length()-1) for a,b in zip(path,path[1:])))
    return {'edges':len(path)-1,'swaps':swaps,'old_191_class':word in refs}

def hamilton(fixed):
    fixed=set(fixed)
    idx={v:i for i,v in enumerate(sorted(fixed))}
    adj=[0]*len(idx); leaves=0
    for v in range(512):
        n=[idx[v^(1<<bit)] for bit in range(9) if v^(1<<bit) in fixed]
        if len(n)==1: leaves|=1<<n[0]
        if len(n)==2:
            a,b=n;adj[a]|=1<<b;adj[b]|=1<<a
    nodes=0
    def dfs(x,avail):
        nonlocal nodes
        nodes+=1
        if not avail:return bool((1<<x)&leaves)
        if not avail&leaves:return False
        reachable=avail|(1<<x); items=avail; endpoints=0
        while items:
            z=items&-items; items-=z; neighbors=adj[z.bit_length()-1]&reachable
            if not neighbors:return False
            if neighbors&(neighbors-1)==0:
                if endpoints or not z&leaves:return False
                endpoints+=1
        choices=adj[x]&avail
        while choices:
            bit=choices&-choices;choices-=bit
            if dfs(bit.bit_length()-1,avail^bit):return True
        return False
    for x in range(len(idx)):
        if leaves&(1<<x) and dfs(x,((1<<len(idx))-1)^(1<<x)):return True,nodes
    return False,nodes
cases=(root/'survivors.log').read_text().splitlines()
assert cases[-1].startswith('DONE')
nodes=0
checked=set()
for line in cases[:-1]:
    raw=line.split(); assert raw[0]=='CASE'
    f=tuple(map(int,raw[1:]));assert len(f)==len(set(f))==96 and f not in checked
    checked.add(f)
    possible,n=hamilton(f);assert not possible;nodes+=n
report={'191_controls':[witness('control.log'),witness('control_3swaps.log')],'surviving_fixed_sets_checked_independently':len(checked),'simple_path_DFS_visits':nodes,'native_radius2':cases[-1],'native_shell3':(root/'shell3.log').read_text().strip()}
print(json.dumps(report,indent=2))
