"""Exact phase constraints for controlled order-three coordinate rotations."""
from pathlib import Path
import argparse,collections,hashlib,itertools,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def canon(v):
    keys=[]
    for w in [v,v[::-1]]:
        labels={};seq=[]
        for x,y in zip(w,w[1:]):
            a=(x^y).bit_length()-1
            if a not in labels:labels[a]=len(labels)
            seq.append(labels[a])
        keys.append(tuple(seq))
    return min(keys)
def valid(v):return len(v)==len(set(v)) and all(((x^v[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(v) for j in range(i+1,len(v)))
def triples(xs):
    if not xs:yield ();return
    a=xs[0]
    for b,c in itertools.combinations(xs[1:],2):
        for rest in triples(tuple(x for x in xs if x not in (a,b,c))):yield ((a,b,c),)+rest
def rotations(n,count):
    for coords in itertools.combinations(range(n),3*count):
        mask=sum(1<<i for i in coords);words=[x for x in range(1<<n) if not x&~mask]
        for cycles in triples(coords):
            for signs0 in itertools.product([1,-1],repeat=count-1):
                signs=(1,)+signs0
                for bits in itertools.product([0,1],repeat=2*count):
                    shift=sum(bits[2*i+j]<<cyc[j] for i,cyc in enumerate(cycles) for j in range(2))
                    tab={}
                    for u in words:
                        x=u^shift;y=0
                        for cyc,sgn in zip(cycles,signs):
                            for j,c in enumerate(cyc):y|=((x>>c)&1)<<cyc[(j+sgn)%3]
                        tab[u]=y^shift
                    yield mask,tab,dict(cycles=cycles,signs=signs,conjugating_shift=shift)
def phase_data(v,n,mask,tab):
    fibres={}
    for x in v:fibres.setdefault(x&~mask,set()).add(x&mask)
    active=sorted(z for z,u in fibres.items() if any(tab[x]!=x for x in u));active_set=set(active)
    parent={z:z for z in active}
    def find(z):
        while parent[z]!=z:parent[z]=parent[parent[z]];z=parent[z]
        return z
    edges=[]
    for z in active:
        for c in range(n):
            if mask>>c&1:continue
            w=z^(1<<c)
            if w not in active_set or z>=w:continue
            a=fibres[z];b=fibres[w];allowed=[]
            for d in range(3):
                image={u:(u if d==0 else tab[u] if d==1 else tab[tab[u]]) for u in a}
                if all((image[u]==q)==(u==q) for u in a for q in b):allowed.append(d)
            assert 0 in allowed
            if len(allowed)<3:edges.append((z,w,allowed))
            if allowed==[0]:parent[find(w)]=find(z)
    groups={}
    for z in active:groups.setdefault(find(z),[]).append(z)
    parts=sorted(groups.values());idx={z:i for i,p in enumerate(parts) for z in p}
    constraints={}
    for z,w,allowed in edges:
        a,b=idx[z],idx[w]
        if a==b:continue
        if a>b:a,b=b,a;allowed=[(-d)%3 for d in allowed]
        constraints.setdefault((a,b),{0,1,2}).intersection_update(allowed)
    return fibres,parts,[(a,b,sorted(ds)) for (a,b),ds in sorted(constraints.items())]
def solutions(parts,edges,limit):
    if not parts:yield [];return
    domains=[{0,1,2} for _ in parts];domains[0]={0};count=0
    def dfs(ds):
        nonlocal count
        ds=[set(s) for s in ds];changed=True
        while changed:
            changed=False
            for a,b,allowed in edges:
                aa={x for x in ds[a] if any((x-y)%3 in allowed for y in ds[b])}
                bb={y for y in ds[b] if any((x-y)%3 in allowed for x in aa)}
                if not aa or not bb:return
                if aa!=ds[a] or bb!=ds[b]:changed=True;ds[a]=aa;ds[b]=bb
        choices=[i for i,s in enumerate(ds) if len(s)>1]
        if not choices:
            count+=1
            if count>limit:raise OverflowError('assignment limit')
            yield [next(iter(s)) for s in ds];return
        i=min(choices,key=lambda j:(len(ds[j]),-sum(j in (a,b) for a,b,_ in edges),j))
        for x in sorted(ds[i]):
            nxt=[set(s) for s in ds];nxt[i]={x};yield from dfs(nxt)
    yield from dfs(domains)
ap=argparse.ArgumentParser();ap.add_argument('--pairs',type=int,choices=[1,2,3],default=1);ap.add_argument('--bank',action='store_true');ap.add_argument('--dimension',type=int,default=8);ap.add_argument('--limit',type=int,default=100000);a=ap.parse_args()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
seedfile=H/'data/lower-dimensional-input.json';bankfile=H/'data/bank9-input.json';seeds=json.loads(seedfile.read_bytes());bank=json.loads(bankfile.read_bytes());known={canon(x['vertex_sequence']) for x in bank}
rows=[('Q'+str(a.dimension),a.dimension,seeds[str(a.dimension)]['vertices'])]
if a.bank:rows=[('bank'+str(i),9,x['vertex_sequence']) for i,x in enumerate(bank)]
start=time.monotonic();results=[];examples=[];new={};status='COMPLETE'
for name,n,v in rows:
    hist=collections.Counter();counts=collections.Counter();nontrivial=[];cases=0
    for mask,tab,desc in rotations(n,a.pairs):
        fibres,parts,edges=phase_data(v,n,mask,tab);hist[len(parts)]+=1;cases+=1;outcomes=[]
        try:
            for phase in solutions(parts,edges,a.limit):
                counts['assignments_mod_global']+=1
                if not any(phase):continue
                f={z:phase[i] for i,p in enumerate(parts) for z in p}
                w=[]
                for x in v:
                    z=x&~mask;u=x&mask;r=f.get(z,0)
                    w.append(z|(u if r==0 else tab[u] if r==1 else tab[tab[u]]))
                assert valid(w)
                key=canon(w);same=key==canon(v);inbank=key in known if n==9 else None
                counts['nonzero_assignments']+=1;counts['different_images']+=not same
                if n==9:counts['outside_bank']+=not inbank
                outcomes.append(dict(phases=phase,same_cube_class=same,in_bank=inbank,moved_indices=[i for i,(x,y) in enumerate(zip(v,w)) if x!=y]))
                if not same and key not in new:
                    ex=dict(seed=name,dimension=n,**desc,mask=mask,parts=parts,constraints=edges,phases=phase,original=v,vertices=w)
                    new[key]=ex
                    if len(examples)<12:examples.append(ex)
        except OverflowError:status='ASSIGNMENT_LIMIT'
        if len(parts)>1:nontrivial.append(dict(**desc,mask=mask,parts=parts,constraints=edges,outcomes=outcomes))
        if status!='COMPLETE':break
        if cases%256==0:
            snap=snapshot()
            if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:status='RESOURCE_LIMIT';break
    result=dict(seed=name,dimension=n,cases=cases,component_histogram=dict(sorted(hist.items())),counts=dict(counts),nontrivial=nontrivial);results.append(result)
    print(name,cases,dict(hist),dict(counts),status,flush=True)
    if status!='COMPLETE':break
out=dict(status=status,cycle_count=a.pairs,records=results,examples=examples,new_classes=len(new),seconds=time.monotonic()-start,resource_gate=gate,source_sha256={str(seedfile):sha(seedfile),str(bankfile):sha(bankfile)},script_sha256=sha(__file__),scope='All indicated order-three rotation subgroups, conjugating translations, and all compatible phase assignments modulo global rotation if COMPLETE. One common generator orientation is removed by inverse equivalence. Native finite calculation only.')
suffix='bank9' if a.bank else 'q'+str(a.dimension)
target=H/'data'/('cyclic-'+str(a.pairs)+'-'+suffix+'.json');target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('SAVED',target.name,status,'seconds',round(out['seconds'],3),'newclasses',len(new))
