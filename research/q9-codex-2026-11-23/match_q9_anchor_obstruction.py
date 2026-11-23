"""Enumerate copies of a fixed obstruction in an induced Q9 path via its longest component."""
import gzip
import json
from collections import Counter
from itertools import permutations
from pathlib import Path

def longest_component(vertices):
    adj={v:[v^(1<<d) for d in range(9) if v^(1<<d) in vertices] for v in vertices}
    paths=[]
    for tip,neighbors in adj.items():
        if len(neighbors)!=1:continue
        chain=[tip,*neighbors]
        while len(adj[chain[-1]])==2:
            chain.append(next(w for w in adj[chain[-1]] if w!=chain[-2]))
        paths.append(chain)
    return min(paths,key=lambda p:(-len(p),p))

def labels(path):
    return [(a^b).bit_length()-1 for a,b in zip(path,path[1:])]

def images(path,chain,anchors):
    found=set()
    for src in [chain,chain[::-1]]:
        source=labels(src)
        flips=labels(path)
        for i in range(len(path)-len(chain)+1):
            target=flips[i:i+len(source)]
            mapping=dict(zip(source,target))
            if any(mapping[a]!=b for a,b in zip(source,target)) or len(mapping)!=len(set(mapping.values())):continue
            spare=sorted(set(range(9))-mapping.keys())
            for dest in permutations(set(range(9))-set(mapping.values())):
                perm=mapping|dict(zip(spare,dest))
                def transform(v):
                    return path[i]^sum(1<<b for a,b in perm.items() if ((v^src[0])>>a)&1)
                candidate=frozenset(map(transform,anchors))
                if candidate<=set(path):
                    found.add(candidate)
    return found

def main():
    cert=Path("q9_junction_integer_audit/unbounded_duals/all66_17429_h0_n16.json")
    anchors=set(json.loads(cert.read_text())["fixed"])
    chain=longest_component(anchors)
    assert len(chain)==15 and len(set(labels(chain)))==7
    with gzip.open("q9_port_followup_public191.txt.gz","rt") as f:
        bank=[list(map(int,line.split())) for line in f]
    rows=[]
    for i,p in enumerate(bank):
        assert len(p)==len(set(p))==192
        assert all(((p[j]^p[k]).bit_count()==1)==(k==j+1) for j in range(len(p)) for k in range(j+1,len(p)))
        im=images(p,chain,anchors)
        if im:rows.append(dict(row=i,copies=len(im)))
    print(json.dumps(dict(anchor_count=len(anchors),longest_component=chain,
                          public_inputs=len(bank),containing=rows)))
if __name__=="__main__":main()
