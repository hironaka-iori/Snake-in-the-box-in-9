"""Complete 28-pair search family for the pinned 98-edge eight-cube parent."""
from itertools import combinations,permutations
import json
import subprocess
from parent_sat import PIN
from parent_geometry import word
from solve import defects


def construct(case):
    raw=subprocess.check_output(["git","show",PIN+":milestones/216-joint-word-support/data/lower-dimensional-input.json"])
    source=json.loads(raw)["8"]["vertices"]
    assert len(source)==99 and source[0]==0 and not defects(source)
    free=list(list(combinations(range(8),6))[case])
    base=[i for i in range(8) if i not in free]
    z=[word(v,base) for v in source]
    groups=[0]
    for a,b in zip(z,z[1:]):groups.append(groups[-1]+(a==b))
    n=groups[-1]+1
    ds=[sum(1<<x for x in range(64) if x.bit_count()%2==g%2) for g in range(n)]
    ds[0]=1;ds[1]=2
    conditions={}
    for i,j in combinations(range(99),2):
        h=(z[i]^z[j]).bit_count();a,b=groups[i],groups[j]
        if a==b:
            assert h==1 if j==i+1 else h>=2
        elif h<2:
            rule={d for d in range(7) if (h+d==1 if j==i+1 else h+d>=2)}
            conditions[(a,b)]=conditions.get((a,b),set(range(7)))&rule
    tables={}
    cons=[]
    for (a,b),dist in sorted(conditions.items()):
        key=(a%2,b%2,tuple(sorted(dist)))
        if key not in tables:
            tables[key]=[sum(1<<y for y in range(64) if y.bit_count()%2==b%2 and (x^y).bit_count() in dist) for x in range(64)]
        cons.append(dict(x=a,y=b,rows=tables[key]))
    ng=[];records=[];seen=set()
    target_columns=[tuple(v>>b&1 for v in source) for b in base]
    for reverse,seq in ((False,source),(True,[v^source[-1] for v in reversed(source)])):
        columns=[tuple(v>>b&1 for v in seq) for b in range(8)]
        fixed_options=[[i for i,c in enumerate(columns) if c==s] for s in target_columns]
        for left in fixed_options[0]:
            for right in fixed_options[1]:
                if left==right:continue
                for free_map in permutations(sorted(set(range(8))-{left,right})):
                    perm=list(range(8))
                    perm[base[0]]=left;perm[base[1]]=right
                    for x,y in zip(free,free_map):perm[x]=y
                    # First normalized free transition uses bit zero.
                    first=groups.index(1)
                    if word(seq[first],free_map)!=1:continue
                    image=[word(v,perm) for v in seq]
                    vals=[None]*n
                    for i,v in enumerate(image):
                        val=word(v,free)
                        assert vals[groups[i]] in (None,val)
                        vals[groups[i]]=val
                    key=tuple(vals)
                    if key in seen:continue
                    seen.add(key);ng.append(vals)
                    records.append(dict(reverse=reverse,output_to_input=perm,vertices=image))
    perms=[[word(v,(0,*p)) for v in range(64)] for p in permutations(range(1,6))]
    return dict(block=free,base=base,z=z,group=groups,variables=n,domains=ds,
                constraints=cons,nogoods=ng,excluded_witnesses=records),perms
