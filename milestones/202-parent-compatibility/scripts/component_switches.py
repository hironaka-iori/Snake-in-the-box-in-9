"""Finite mathematical census of coordinate-swap components on saved snakes."""
from pathlib import Path
import collections,hashlib,itertools,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def canonical(v):
    out=[]
    for w in (v,v[::-1]):
        labels={};t=[]
        for x,y in zip(w,w[1:]):
            d=(x^y).bit_length()-1
            if d not in labels:labels[d]=len(labels)
            t.append(labels[d])
        out.append(tuple(t))
    return min(out)
def components(v,n,a,b,parity):
    mask=(1<<a)|(1<<b)
    active={x&~mask for x in v if (((x>>a)^(x>>b))&1)==parity}
    unseen=set(active);out=[]
    while unseen:
        start=min(unseen);todo=[start];unseen.remove(start);part=[]
        while todo:
            z=todo.pop();part.append(z)
            for c in range(n):
                if c in (a,b):continue
                w=z^(1<<c)
                if w in unseen:unseen.remove(w);todo.append(w)
        out.append(sorted(part))
    return sorted(out,key=lambda x:(len(x),x))
def image(v,a,b,parity,part):
    mask=(1<<a)|(1<<b);part=set(part)
    return [x^mask if (((x>>a)^(x>>b))&1)==parity and (x&~mask) in part else x for x in v]
def valid(v,n):
    return len(v)==len(set(v)) and all(0<=x<1<<n for x in v) and all(((x^v[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(v) for j in range(i+1,len(v)))
seedfile=H/'data/lower-dimensional-input.json'
bankfile=H/'data/bank9-input.json';seeds=json.loads(seedfile.read_bytes());bank=json.loads(bankfile.read_bytes())
known={canonical(row['vertex_sequence']) for row in bank}
rows=[('Q'+n,int(n),d['vertices']) for n,d in seeds.items()]+[('bank'+str(i),9,d['vertex_sequence']) for i,d in enumerate(bank)]
records=[];examples=[];classes=set();singleimages=0
for name,n,v in rows:
    counts=collections.Counter();nontrivial=[]
    for a,b in itertools.combinations(range(n),2):
        for parity in [0,1]:
            parts=components(v,n,a,b,parity);counts[len(parts)]+=1
            if len(parts)<=1:continue
            outcomes=[]
            for part in parts:
                w=image(v,a,b,parity,part)
                assert valid(w,n),(name,a,b,parity,part)
                same=canonical(w)==canonical(v);singleimages+=1
                outcomes.append(dict(component=part,moved_indices=[i for i,(x,y) in enumerate(zip(v,w)) if x!=y],same_cube_class=same,in_bank=canonical(w) in known if n==9 else None))
                if n==9:classes.add(canonical(w))
                if not same and len(examples)<12:
                    changed=next((i,j,(v[i]^v[j]).bit_count(),(w[i]^w[j]).bit_count()) for i in range(len(v)) for j in range(i+1,len(v)) if (v[i]^v[j]).bit_count()!=(w[i]^w[j]).bit_count())
                    examples.append(dict(seed=name,dimension=n,coordinates=[a,b],parity=parity,component=part,vertices=v,image=w,distance_change=changed))
            nontrivial.append(dict(coordinates=[a,b],parity=parity,components=parts,outcomes=outcomes))
    records.append(dict(seed=name,dimension=n,edges=len(v)-1,component_count_distribution=dict(sorted(counts.items())),nontrivial=nontrivial))
summary=dict(sources={str(seedfile):sha(seedfile),str(bankfile):sha(bankfile)},script_sha256=sha(Path(__file__)),definition='Switch the active parity diagonal in selected connected components of its projection graph; both diagonals are included.',
             records=records,examples=examples,single_component_images=singleimages,q9_image_classes=len(classes),q9_classes_outside_bank=len(classes-known),
             scope='Native component census and single-component images. Arbitrary subsets and iterations are covered by the separate complement, equivariance and closure argument when every component count is at most three; they were not individually enumerated.')
(H/'data/component-switches.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(lower_dimensions=[{k:r[k] for k in ['seed','component_count_distribution']} for r in records if r['dimension']<9],
                     q9_distribution=dict(collections.Counter(max(map(int,r['component_count_distribution'])) for r in records if r['dimension']==9)),
                     images=singleimages,q9_image_classes=len(classes),q9_classes_outside_bank=len(classes-known),examples=len(examples))))
