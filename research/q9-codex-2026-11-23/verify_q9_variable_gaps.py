from pathlib import Path
from itertools import combinations
import json,random,subprocess
def valid(p):
    return len(p)==len(set(p)) and all(0<=v<512 for v in p) and all(((x^p[j]).bit_count()==1)==(i+1==j) for i,x in enumerate(p) for j in range(i+1,len(p)))
def ask(p,sections,goal,extra):
    args=[goal,extra,len(p),*p,len(sections)]
    for a,b in sections:args.extend([a,b])
    out=subprocess.check_output(["/tmp/q9var-query-21","query"],input=" ".join(map(str,args))+"\n",text=True).split()
    assert out[0]!="UNKNOWN"
    if out[0]=="NO":return None
    assert out[0]=="YES";w=list(map(int,out[1:]));assert valid(w) and len(w)==goal+1
    offsets=[w.index(p[a]) for a,b in sections]
    for k,(a,b) in enumerate(sections):assert w[offsets[k]:offsets[k]+b-a+1]==p[a:b+1]
    distances=[offsets[0]]+[offsets[k]-offsets[k-1]-(sections[k-1][1]-sections[k-1][0]) for k in range(1,len(sections))]+[len(w)-1-offsets[-1]-(sections[-1][1]-sections[-1][0])]
    caps=[sections[0][0]+extra]+[a2-b+extra for (_,b),(a2,_) in zip(sections,sections[1:])]+[len(p)-1-sections[-1][1]+extra]
    assert all(0<=a<=b for a,b in zip(distances,caps))
    return w
def shortcut_control():
    for row,line in enumerate(open("q9_odd_reference_vertices.txt")):
        p=list(map(int,line.split()));s=set(p);short=[]
        for i in range(1,len(p)-5):
            diff=p[i]^p[i+4]
            if diff.bit_count()!=2:continue
            for d in range(9):
                x=p[i]^(1<<d)
                if not(diff>>d&1) or x in s:continue
                if all((x^y).bit_count()!=1 for y in p[:i]+p[i+5:]):short.append((i,x))
        for (i,x),(j,y) in combinations(short,2):
            if j<=i+6:continue
            q=p[:i+1]+[x]+p[i+4:j+1]+[y]+p[j+4:]
            if not valid(q):continue
            sections=[(0,i),(i+2,j-2),(j,len(q)-1)]
            # Each gap must regain its two missing edges, with the ends pinned by the reconstruction check below.
            w=ask(q,sections,191,2)
            if w and w[:i+1]==q[:i+1] and w[-(len(q)-j):]==q[j:] and w.index(q[j])-w.index(q[j-2])==4 and w.index(q[i+2])-w.index(q[i])==4:
                return dict(reference_row=row,shortened_edges=len(q)-1,recovered_edges=len(w)-1,shortened_starts=[i,j],restored_bridge_lengths=[4,4])
    raise ValueError("No two-gap positive control")
# Independent small tests. Starting from a complete left island, extend by ordinary
# induced-walk DFS; the chosen endpoint length determines the intermediate gap.
def brute(p,goal,extra):
    left=p[:2];right=p[-2:];maxgap=len(p)-3+extra
    def rec(w):
        if len(w)>goal+1:return False
        if len(w)==goal+1:
            for i in range(extra+1):
                if w[i:i+2]!=left:continue
                for j in range(i+3,len(w)-1):
                    if w[j:j+2]==right and j-i-1<=maxgap and len(w)-2-j<=extra:return True
            return False
        if right[-1] in w and right[0] not in w:return False
        if right[0] not in w and (w[-1]^right[0]).bit_count()>goal-len(w):return False
        for d in range(9):
            v=w[-1]^(1<<d)
            if v in w or any((z^v).bit_count()==1 for z in w[:-1]):continue
            if rec(w+[v]):return True
        return False
    starts=[left[0]] if extra==0 else [left[0]]+[left[0]^(1<<d) for d in range(9) if left[0]^(1<<d)!=left[1]]
    return any(rec(left if v==left[0] else [v]+left) for v in starts if v==left[0] or valid([v]+left))
rng=random.Random(88191);yes=no=0
for j in range(36):
    axes=rng.sample(range(9),5);p=[0]
    for d in axes:p.append(p[-1]^(1<<d))
    target=3+j%5;extra=(j//5)%2
    r=ask(p,[(0,1),(4,5)],target,extra) is not None
    assert r==brute(p,target,extra),(p,target,extra,r)
    yes+=r;no+=not r
print(json.dumps(dict(shortcut=shortcut_control(),small_yes=yes,small_no=no),indent=2))
