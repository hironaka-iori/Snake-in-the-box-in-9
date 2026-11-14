"""Census of simultaneous two-pair controlled reflections on saved paths."""
from pathlib import Path
import argparse,collections,hashlib,itertools,json,time
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def canon(v):
    result=[]
    for w in [v,v[::-1]]:
        names={};out=[]
        for x,y in zip(w,w[1:]):
            d=(x^y).bit_length()-1
            if d not in names:names[d]=len(names)
            out.append(names[d])
        result.append(tuple(out))
    return min(result)
def image_table(pairing,epsilon,n):
    bits=sum(1<<a for pair in pairing for a in pair)
    table={}
    for t in range(1<<n):
        if t&~bits:continue
        u=t
        for (a,b),e in zip(pairing,epsilon):
            if (((t>>a)^(t>>b))&1)==e:u^=(1<<a)|(1<<b)
        table[t]=u
    return bits,table
def parts_for(v,n,mask,table):
    fibres={};active=set()
    for x in v:
        z=x&~mask;u=x&mask
        if table[u]!=u:
            active.add(z);fibres.setdefault(z,set()).add(min(u,table[u]))
    unseen=set(active);parts=[]
    while unseen:
        root=min(unseen);todo=[root];unseen.remove(root);part=[]
        while todo:
            z=todo.pop();part.append(z)
            for a in range(n):
                if (mask>>a)&1:continue
                w=z^(1<<a)
                if w in unseen and fibres[z]&fibres[w]:unseen.remove(w);todo.append(w)
        parts.append(sorted(part))
    return sorted(parts,key=lambda p:(len(p),p)),fibres
def valid(v):
    return len(v)==len(set(v)) and all(((x^v[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(v) for j in range(i+1,len(v)))

ap=argparse.ArgumentParser();ap.add_argument('--bank',action='store_true');ap.add_argument('--limit',type=int);args=ap.parse_args()
seedfile=H/'data/lower-dimensional-input.json';bankfile=H/'data/bank9-input.json'
seeds=json.loads(seedfile.read_bytes());bank=json.loads(bankfile.read_bytes());known={canon(x['vertex_sequence']) for x in bank}
rows=[('Q'+n,int(n),seeds[n]['vertices']) for n in ['6','7','8']]
if args.bank:rows=[('bank'+str(i),9,x['vertex_sequence']) for i,x in enumerate(bank[:args.limit])]
start=time.monotonic();records=[];examples=[];newclasses={};totalimages=0
for name,n,v in rows:
    distribution=collections.Counter();nontrivial=[];images=set();different=0
    for a,b,c,d in itertools.combinations(range(n),4):
        for pairing in [((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))]:
            for epsilon in itertools.product([0,1],repeat=2):
                mask,table=image_table(pairing,epsilon,n);parts,fibres=parts_for(v,n,mask,table);distribution[len(parts)]+=1
                if len(parts)<=1:continue
                outcomes=[]
                # Enumerate every component subset modulo global reflection.
                assert len(parts)<=16,(name,pairing,epsilon,len(parts))
                for choice in range(1,1<<(len(parts)-1)):
                    selected={z for i,p in enumerate(parts) if (choice>>i)&1 for z in p}
                    w=[(x&~mask)|table[x&mask] if (x&~mask) in selected else x for x in v]
                    assert valid(w),(name,pairing,epsilon,choice)
                    key=canon(w);images.add(key);totalimages+=1;same=key==canon(v)
                    if not same:different+=1
                    outcomes.append(dict(choice=choice,moved_indices=[i for i,(x,y) in enumerate(zip(v,w)) if x!=y],same_cube_class=same,in_bank=key in known if n==9 else None))
                    if not same and n<9 and key not in newclasses:
                        newclasses[key]=dict(seed=name,dimension=n,pairing=pairing,epsilon=epsilon,parts=parts,choice=choice,vertices=w,original=v)
                    if not same and len(examples)<8:examples.append(dict(seed=name,pairing=pairing,epsilon=epsilon,parts=parts,choice=choice,original=v,vertices=w))
                nontrivial.append(dict(pairing=pairing,epsilon=epsilon,parts=parts,outcomes=outcomes))
    record=dict(seed=name,dimension=n,edges=len(v)-1,distribution=dict(sorted(distribution.items())),nontrivial=nontrivial,image_classes=len(images),different_images=different)
    records.append(record)
    print(name,dict(sorted(distribution.items())),'classes',len(images),'changed',different,flush=True)
data=dict(sources={str(seedfile):sha(seedfile),str(bankfile):sha(bankfile)},script_sha256=sha(Path(__file__)),records=records,examples=examples,
          new_lower_dimensional_shapes=list(newclasses.values()),total_images=totalimages,seconds=time.monotonic()-start,
          scope='All four-coordinate sets, three pairings and both diagonal choices for each pair; every selector subset modulo the global involution for each input. Native census, not a Lean replay.')
name='bank-block-census'+('-'+str(args.limit) if args.limit is not None else '')+'.json' if args.bank else 'parent-block-census.json'
(H/'data'/name).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print('SAVED',name,'seconds',round(data['seconds'],3),'images',totalimages,'new lower shapes',len(newclasses))
