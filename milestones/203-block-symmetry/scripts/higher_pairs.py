"""Finish the nontrivial involutive-block cases on the saved Q8 parent."""
from pathlib import Path
import collections,hashlib,itertools,json,time
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pairings(xs):
    if not xs:yield ();return
    a=xs[0]
    for b in xs[1:]:
        for rest in pairings(tuple(x for x in xs[1:] if x!=b)):yield ((a,b),)+rest
def canon(v):
    out=[]
    for w in [v,v[::-1]]:
        labels={};seq=[]
        for x,y in zip(w,w[1:]):
            d=(x^y).bit_length()-1
            if d not in labels:labels[d]=len(labels)
            seq.append(labels[d])
        out.append(tuple(seq))
    return min(out)
def valid(v):return len(v)==len(set(v)) and all(((x^v[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(v) for j in range(i+1,len(v)))
seedfile=H/'data/lower-dimensional-input.json';parentfile=H/'data/parent-block-census.json'
d=json.loads(seedfile.read_bytes());new=json.loads(parentfile.read_bytes())['new_lower_dimensional_shapes'][0]['vertices']
records=[];start=time.monotonic()
for name,n,v in [('Q7-original',7,d['7']['vertices']),('Q7-new',7,new),('Q8',8,d['8']['vertices'])]:
    hist=collections.Counter();examples=[];classes=set()
    for coords in itertools.combinations(range(n),6):
        mask=sum(1<<a for a in coords)
        blocks=[x for x in range(1<<n) if not x&~mask]
        for pairs in pairings(coords):
            for eps in itertools.product([0,1],repeat=3):
                h={}
                for x in blocks:
                    y=x
                    for (a,b),e in zip(pairs,eps):
                        if (((x>>a)^(x>>b))&1)==e:y^=(1<<a)|(1<<b)
                    h[x]=y
                fibres={}
                for x in v:
                    z=x&~mask;u=x&mask
                    if h[u]!=u:fibres.setdefault(z,set()).add(min(u,h[u]))
                unseen=set(fibres);parts=[]
                while unseen:
                    todo=[min(unseen)];unseen.remove(todo[0]);part=[]
                    while todo:
                        z=todo.pop();part.append(z)
                        for a in range(n):
                            if (mask>>a)&1:continue
                            w=z^(1<<a)
                            if w in unseen and fibres[z]&fibres[w]:unseen.remove(w);todo.append(w)
                    parts.append(sorted(part))
                parts.sort(key=lambda p:(len(p),p));hist[len(parts)]+=1
                for choice in range(1,1<<(len(parts)-1)):
                    selected={z for i,p in enumerate(parts) if (choice>>i)&1 for z in p}
                    w=[(x&~mask)|h[x&mask] if (x&~mask) in selected else x for x in v]
                    assert valid(w)
                    key=canon(w);classes.add(key)
                    if key!=canon(v):examples.append(dict(pairs=pairs,epsilon=eps,parts=parts,choice=choice,vertices=w))
    r=dict(seed=name,dimension=n,distribution=dict(sorted(hist.items())),image_classes=len(classes),changed_examples=examples)
    records.append(r);print(name,dict(hist),'changed',len(examples),flush=True)
out=dict(records=records,seconds=time.monotonic()-start,sources={str(seedfile):sha(seedfile),str(parentfile):sha(parentfile)},script_sha256=sha(Path(__file__)),
         scope='All three-pair reflections and all selector subsets modulo global reflection on these three parents. Numerical census only; four pairs inQ8 leave no selector coordinates and are ordinary global isometries.')
(H/'data/three-pair-census.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('SAVED three-pair-census.json',round(out['seconds'],3),'seconds')
