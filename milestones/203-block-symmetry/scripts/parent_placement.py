"""Exact placement and trimming comparison for the newly switched Q7 parent."""
from pathlib import Path
import collections,hashlib,itertools,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
source=H/'data/parent-block-census.json';d=json.loads(source.read_bytes())
assert len(d['new_lower_dimensional_shapes'])==1
row=d['new_lower_dimensional_shapes'][0];old=row['original'];new=row['vertices'];cap=10;records=[];start=time.monotonic()
for name,p,q in [('original-new',old,new),('new-new',new,new)]:
    index={v:i for i,v in enumerate(p)};hist=collections.Counter();best=0;witnesses=[];eligible=0;intervals=0;status='COMPLETE';done=0
    for perm in itertools.permutations(range(7)):
        images=[sum(((v>>k)&1)<<perm[k] for k in range(7)) for v in q];counts=[0]*128
        for u in p:
            for v in images:counts[u^v]+=1
        hist.update(counts);done+=1
        for t,c in enumerate(counts):
            if c>cap:continue
            eligible+=1;collisions=[(index[v^t],j) for j,v in enumerate(images) if v^t in index]
            assert len(collisions)==c
            for left in range(cap+1):
                for right in range(cap-left+1):
                    intervals+=1;forbidden=[j for i,j in collisions if left<=i<51-right]
                    cuts=[-1]+forbidden+[51]
                    gap=max((b-a-1,a+1,b) for a,b in zip(cuts,cuts[1:]));total=51-left-right+gap[0]
                    if total<102-cap:continue
                    item=dict(permutation=perm,translation=t,overlap=c,collisions=collisions,first_interval=[left,51-right],second_interval=[gap[1],gap[2]],vertices=total)
                    if total>best:best=total;witnesses=[]
                    if total==best and len(witnesses)<4:
                        paths=[p[left:51-right],[128+(v^t) for v in images[gap[1]:gap[2]]]]
                        assert all((x^y).bit_count()!=1 for x in paths[0] for y in paths[1])
                        for path in paths:assert all(((x^path[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(path) for j in range(i+1,len(path)))
                        item['paths']=paths;witnesses.append(item)
        if done%256==0:
            snap=snapshot()
            if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:status='RESOURCE_LIMIT';break
    if status=='COMPLETE' and best<102-cap:status='THRESHOLD_NOT_ATTAINED'
    r=dict(pair=name,status=status,permutations=done,isometries=128*done,minimum_overlap=min(hist),histogram=dict(sorted(hist.items())),maximum_trimmed_vertices=best,eligible=eligible,intervals=intervals,witnesses=witnesses)
    records.append(r);print(name,status,'minimum overlap',min(hist),'trim maximum',best,flush=True)
out=dict(records=records,seconds=time.monotonic()-start,omission_cap=cap,resource_gate=gate,source_sha256=sha(source),script_sha256=sha(Path(__file__)),scope='All cube isometries for original/new and new/new Q7 pairs. If COMPLETE, attaining92 vertices makes the ten-omission trimming cutoff exhaustive; numerical census only.')
(H/'data/parent-placement.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('SAVED parent-placement.json',round(out['seconds'],3),'seconds')
