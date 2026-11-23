import collections,json,subprocess,sys
from pathlib import Path
def edges(p):
    index={x:i for i,x in enumerate(p)}
    assert len(index)==len(p) and min(p)>=0 and max(p)<512
    adj={(i,j) for i,x in enumerate(p) for d in range(9) if (j:=index.get(x^(1<<d),-1))>i}
    ordinary={(i,i+1) for i in range(len(p)-1)}
    assert ordinary <= adj
    return adj-ordinary
def allpairs(p):
    assert len(p)==len(set(p))==191
    return all(((x^p[j]).bit_count()==1)==(j-i==1) for i,x in enumerate(p) for j in range(i+1,len(p)))
seen={tuple(map(int,l.split())) for l in open("q9_onechord_minority_sets.txt")}
dist=collections.Counter()
for line in open("q9_face_donor_walks.txt"):
    p=list(map(int,line.split()));assert len(p)==193
    extra=edges(p);assert 1<=len(extra)<=6
    half=tuple(sorted(p[1::2]));assert half not in seen;seen.add(half);dist[len(extra)]+=1
p=[0]
for s in open("q9_reordered_segments_20261120/reference191.words").readline().strip()[:-1]:p.append(p[-1]^(1<<int(s)))
assert allpairs(p)
bad=p.copy();flipped=[]
for i in range(1,len(p)-1,2):
    other=p[i-1]^p[i]^p[i+1]
    if other in bad:continue
    q=bad.copy();q[i]=other
    if len(edges(q))>len(edges(bad)):
        bad=q;flipped.append(i)
    if len(flipped)==2:break
assert len(flipped)==2 and edges(bad)
r=subprocess.run([sys.argv[1],"3000","1887","5","5","5000",*sys.argv[2:]],input=" ".join(map(str,bad))+"\n",text=True,capture_output=True,check=True)
l=next(line for line in r.stdout.splitlines() if line.startswith("FOUND "));repair=list(map(int,l.split()[1:]));assert allpairs(repair) and repair!=bad
print(json.dumps(dict(unique_new_sets=sum(dist.values()),input_chords=dist,control_input_chords=len(edges(bad)),control_changed_positions=flipped,control_repaired_edges=len(repair)-1,control_log=r.stdout.splitlines()[-1]),indent=2))
