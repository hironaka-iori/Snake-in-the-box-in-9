"""Check multilayer deletion search against independent DFS and a Q9 record."""
import gzip,json,random,subprocess,sys
from verify_q9_center_avoidance import verify
rng=random.Random(241308)
def arm(dim):
    p=[rng.randrange(1<<dim)]
    while True:
        c=[p[-1]^(1<<d) for d in range(dim) if (p[-1]^(1<<d)) not in p and
           all((w^p[-1]^(1<<d)).bit_count()!=1 for w in p[:-1])]
        if not c:return p
        p.append(rng.choice(c))

def oracle(vertices):
    best=[0,0]
    def walk(p,used,changes):
        if changes<=1:best[0]=max(best[0],len(p)-1)
        best[1]=max(best[1],len(p)-1)
        for v in vertices-used:
            if (v^p[-1]).bit_count()!=1 or any((v^u).bit_count()==1 for u in p[:-1]):continue
            walk(p+[v],used|{v},changes+int((v^p[-1])==256))
    for x in vertices:walk([x],{x},0)
    return best
program=sys.argv[1]
rows=[];answers=[];cases=0;multicross=0
for i in range(160):
    dim=3+i%2
    a=arm(dim);b=arm(dim);vertices=set(a)|{256+x for x in b}
    first,maximum=oracle(vertices)
    multicross+=int(maximum>first);cases+=1
    for target in (maximum,maximum+1):
        rows.append(" ".join(map(str,[target,len(a),len(b),*a,*b])))
        answers.append((target,maximum,vertices))
out=subprocess.run([program,"--fixed"],input="\n".join(rows)+"\n",text=True,
                   capture_output=True,check=True).stdout.splitlines()
assert len(out)==len(answers)
for line,(target,maximum,verts) in zip(out,answers):
    entry=line.split()
    assert (entry[0]=="FOUND")==(target<=maximum)
    if entry[0]=="FOUND":
        p=list(map(int,entry[1:]));verify(p);assert len(p)==target+1 and set(p)<=verts
assert multicross>0
r=json.loads(open("q9_record_single_crossing_191.jsonl").readline())
steps=list(map(int,r["steps"]));axis=next(x for x in range(9) if steps.count(x)==1);k=steps.index(axis)
def pack(ds):return "".join(str(d-int(d>axis)) for d in ds)
out=subprocess.run([program,"191","1","0"],input=pack(steps[:k])+"\n"+pack(steps[k+1:])+"\n",
                   text=True,capture_output=True,check=True).stdout.split()
assert out[0]=="FOUND"
p=list(map(int,out[3:]));verify(p);assert len(p)==192
print(json.dumps(dict(small_domains=cases,independent_decisions=len(answers),
                      domains_requiring_multiple_crossings_for_optimum=multicross,
                      q9_control_edges=len(p)-1,q9_control_vertices=p),separators=(",",":")))
