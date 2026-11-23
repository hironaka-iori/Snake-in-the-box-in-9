"""Independent checks of route joins and complete corner/endpoint enumeration logs."""
from pathlib import Path
import random,json,subprocess,sys
from collections import Counter

def path(word):
    p=[0]
    for c in word.strip():p.append(p[-1]^(1<<int(c)))
    return p
def valid(p):
    return len(p)==len(set(p)) and all(0<=v<512 for v in p) and all(
        ((v^p[j]).bit_count()==1)==(i+1==j) for i,v in enumerate(p) for j in range(i+1,len(p)))
def brute(anchors,lens,left,right):
    # Fix start at the first anchor, build the rightward portion then the left tip.
    at={0:anchors[0]};n=0
    for v,g in zip(anchors[1:],lens):n+=g;at[n]=v
    original=n
    def grow(p,remain,back):
        if back and remain==0:return True
        t=len(p)
        if not back and t>original+right:
            return grow(p[::-1],left,True)
        for d in range(9):
            v=p[-1]^(1<<d)
            if not back and t in at and v!=at[t]:continue
            if not back and any((v^a).bit_count()>j-t for j,a in at.items() if j>t):continue
            if v in p or any((v^w).bit_count()==1 for w in p[:-1]):continue
            if grow(p+[v],remain-1 if back else remain,back):return True
        return False
    return grow([anchors[0]],0,False)
rng=random.Random(44118)
bank=[path(s) for s in open("q9_reordered_segments_20261120/reference191.words")]
assert len(bank)==131 and all(map(valid,bank))
cases=[]
for i in range(120):
    p=rng.choice(bank);j=rng.randrange(170);g=rng.randrange(2,6);h=rng.randrange(2,6)
    a=[p[j],p[j+g],p[j+g+h]];lens=[g,h]
    if i%3==0 and g>=4:lens[0]-=2
    if i%4==0:a[-1]^=3
    if min((x^y).bit_count() for k,x in enumerate(a) for y in a[k+1:])<2:continue
    l,r=rng.randrange(2),rng.randrange(2)
    cases.append((a,lens,l,r,brute(a,lens,l,r)))
# A long positive control has known witnesses at the prescribed anchor times.
p=bank[0];times=list(range(2,189,4))
cases.append(([p[t] for t in times],[4]*(len(times)-1),2,191-times[-1],True))
lines=[" ".join(map(str,[len(a),l,r,*a,*g])) for a,g,l,r,_ in cases]
data=subprocess.run([sys.argv[1]],input="\n".join(lines)+"\n",capture_output=True,text=True,check=True).stdout.splitlines()
assert len(data)==len(cases)
stat=Counter()
for line,(a,g,l,r,expected) in zip(data,cases):
    ok,cap,*w=map(int,line.split())
    assert not cap and bool(ok)==expected
    if ok:
        assert valid(w) and len(w)==l+r+sum(g)+1
        k=l;assert w[k]==a[0]
        for cost,v in zip(g,a[1:]):k+=cost;assert w[k]==v
    stat["positive" if ok else "negative"]+=1

def corners(files,target,records,minimum,maximum):
    rows={}
    for name in files:
        for line in open(name):
            typ,idx,trim,tests,cap,nodes,var=line.split();assert typ=="ROW"
            i,t,k,c=map(int,(idx,trim,tests,cap));assert k==(t+1)*(t+1+192-target)
            rows[i,t]=k,c
    assert set(rows)=={(i,t) for i in range(records) for t in range(minimum,maximum+1)}
    return {"cases":sum(k for k,c in rows.values()),"cutoffs":sum(c for k,c in rows.values())}
def summary(name):
    line=Path(name).read_text().splitlines()[-1].split();assert line[0]=="DONE"
    trials,excluded,cutoff,nodes=map(int,line[1:]);assert trials==excluded+cutoff
    return {"draws":trials,"excluded":excluded,"cutoffs":cutoff}
print(json.dumps({"corner_records_191":corners(["q9_corners_tips16.log","q9_corners_tips34.log","q9_corners_tips34_deep.log"],191,131,0,34),
"corner_records_190":corners(["q9_corners_190_donors.log"],190,1042,0,19),
"corner_controls":json.loads(Path("q9_corner_crosscheck.json").read_text()),"route_controls":stat,
"route_draws":{k:summary("q9_short_routes_"+k+".log") for k in ("records","onechord","190")}},indent=2))
