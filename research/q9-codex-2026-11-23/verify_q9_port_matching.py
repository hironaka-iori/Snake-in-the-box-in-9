from itertools import permutations,product
import subprocess,json,random
from pathlib import Path
def valid(p):
    return len(p)==len(set(p)) and all(0<=v<512 for v in p) and all(((a^p[j]).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j in range(i+1,len(p)))
def query(islands,target,bridge,arm):
    vals=[target,bridge,arm,len(islands)]
    for p in islands:vals.extend([len(p),*p])
    out=subprocess.check_output(["/tmp/q9verifyports21"],input=" ".join(map(str,vals))+"\n",text=True).split()
    assert out[0]!="UNKNOWN"
    if out[0]=="NO":return None
    p=list(map(int,out[1:]));assert len(p)==target+1 and valid(p)
    where=[]
    for island in islands:
        loc=sorted(p.index(v) for v in island);assert loc[-1]-loc[0]+1==len(island) and p[loc[0]:loc[-1]+1] in [island,island[::-1]]
        where.append((loc[0],loc[-1]))
    where.sort();assert where[0][0]<=arm and len(p)-1-where[-1][1]<=arm
    assert all(c-b<=bridge for (_,b),(c,_) in zip(where,where[1:]))
    return p
def brute(islands,goal):
    # No free arms, bridges of at most three edges; enumerate orders and build each actual walk.
    def connect(p,left,b):
        if len(left)==0:return len(p)==goal+1
        q=left[0]
        if (p[-1]^q[0]).bit_count()==1 and valid(p+q) and connect(p+q,left[1:],3):return True
        if b==1 or len(p)>=goal:return False
        for d in range(9):
            v=p[-1]^1<<d
            if (v^q[0]).bit_count()>b-1 or not valid(p+[v]):continue
            if connect(p+[v],left,b-1):return True
        return False
    for pieces in permutations(islands):
        for mask in product((False,True),repeat=len(islands)):
            oriented=[q[::-1] if m else q for q,m in zip(pieces,mask)]
            if connect(oriented[0],oriented[1:],3):return True
    return False
small={}
for l in open("q9_odd_reference_vertices.txt").read().splitlines()[:4]:
    p=list(map(int,l.split()))
    for gap in (2,3,4):
        islands=[p[:2],p[gap+1:gap+3],p[2*gap+2:2*gap+4]]
        for goal in (5,6,7,8,9,10):
            got=query(islands,goal,3,0) is not None
            assert brute(islands,goal)==got
            small[str(got)]=small.get(str(got),0)+1
# Keep three disjoint islands and reverse and reorder them before passing to the matcher.
p=list(map(int,open("q9_odd_reference_vertices.txt").read().splitlines()[105].split()))
islands=[p[52:][::-1],p[:16],p[19:49][::-1]]
w=query(islands,191,4,0);assert w
# Damage a verified 191 path with two separate corner flips and validate a repair.
bad=p.copy();flips=[]
def loss(p):return sum((x^y).bit_count()==1 for i,x in enumerate(p) for y in p[i+2:])
for i in range(1,len(p)-1,2):
    q=bad.copy();q[i]=bad[i-1]^bad[i]^bad[i+1]
    if len(set(q))==len(q) and loss(q)>loss(bad):bad=q;flips.append(i)
    if len(flips)==2:break
word="".join(str((a^b).bit_length()-1) for a,b in zip(bad,bad[1:]))
out=subprocess.check_output(["/tmp/q9repairports21","4000",str(loss(bad)),"2","3","191","3187"],input=f"{loss(bad)} {word}\n",text=True)
line=next(l for l in out.splitlines() if l.startswith("FOUND "));w2=list(map(int,line.split()[3:]));assert len(w2)==192 and valid(w2)
print(json.dumps(dict(small=small,reorder_edges=len(w)-1,chord_control_input_loss=loss(bad),chord_control_output_edges=len(w2)-1),indent=2))
