"""Exact whole-snake gluing of independently chosen cube isometries on slices."""
from pathlib import Path
import argparse,collections,hashlib,itertools,json,math,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1]
def canon(v):
    out=[]
    for w in [v,v[::-1]]:
        names={};seq=[]
        for x,y in zip(w,w[1:]):
            a=(x^y).bit_length()-1
            if a not in names:names[a]=len(names)
            seq.append(names[a])
        out.append(tuple(seq))
    return min(out)
def valid(v):return len(v)==len(set(v)) and all(((x^v[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(v) for j in range(i+1,len(v)))
def pack(x,coords):return sum(((x>>a)&1)<<i for i,a in enumerate(coords))
def unpack(x,coords):return sum(((x>>i)&1)<<a for i,a in enumerate(coords))
def relative(A,B,k):
    common=sorted(A&B);assert common;anchor=common[0];cells={}
    for c in range(k):cells.setdefault(tuple(((u^anchor)>>c)&1 for u in common),[]).append(c)
    groups=list(cells.values());out=[]
    for images in itertools.product(*(itertools.permutations(cell) for cell in groups)):
        pi={a:b for cell,image in zip(groups,images) for a,b in zip(cell,image)}
        tab=tuple(anchor^sum((((u^anchor)>>a)&1)<<pi[a] for a in range(k)) for u in range(1<<k))
        if any(tab[u] in A for u in B-A):continue
        out.append(tab)
    return out,dict(crossings=common,cells=groups,stabilizer_size=math.prod(math.factorial(len(c)) for c in groups),admissible=len(out))
ap=argparse.ArgumentParser();ap.add_argument('--base-size',type=int,choices=range(1,7),default=2);ap.add_argument('--seconds',type=float,default=30);ap.add_argument('--nodes',type=int,default=100000);a=ap.parse_args()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
source=H/'data/lower-dimensional-input.json';v=json.loads(source.read_bytes())['8']['vertices'];known=canon(v);start=time.monotonic();rows=[];examples=[];allclasses=set();status='COMPLETE'
for basecoords in itertools.combinations(range(8),a.base_size):
    blockcoords=[x for x in range(8) if x not in basecoords];k=len(blockcoords);vertices=[(pack(x,basecoords),pack(x,blockcoords)) for x in v];fibres={}
    for z,u in vertices:fibres.setdefault(z,set()).add(u)
    occupied=sorted(fibres);rels={};edgeinfo=[]
    for z in occupied:
        for w in occupied:
            if z>=w or (z^w).bit_count()!=1 or not fibres[z]&fibres[w]:continue
            ts,info=relative(fibres[z],fibres[w],k);rels[z,w]=ts
            inverses=[]
            for t in ts:
                inv=[0]*len(t)
                for i,j in enumerate(t):inv[j]=i
                inverses.append(tuple(inv))
            rels[w,z]=inverses;edgeinfo.append(dict(base_edge=[z,w],**info))
    identity=tuple(range(1<<k));assigned={occupied[0]:identity};nodes=0;solutions=0;classes=set();changed=0
    def compatible(z,g):
        A=fibres[z];imgA={g[u] for u in A}
        for w,h in assigned.items():
            if (z^w).bit_count()!=1:continue
            B=fibres[w];common=A&B
            if any(g[u]!=h[u] for u in common):return False
            if len(imgA&{h[u] for u in B})!=len(common):return False
        return True
    def dfs():
        nonlocal_placeholder=None
        global nodes,solutions,changed,status
        nodes+=1
        if nodes>a.nodes or time.monotonic()-start>a.seconds:raise TimeoutError
        if len(assigned)==len(occupied):
            solutions+=1;w=[unpack(z,basecoords)|unpack(assigned[z][u],blockcoords) for z,u in vertices];assert valid(w)
            key=canon(w);classes.add(key);allclasses.add(key)
            if key!=known:
                changed+=1
                if len(examples)<12:examples.append(dict(base_coordinates=basecoords,block_coordinates=blockcoords,maps={z:list(t) for z,t in assigned.items()},vertices=w,original=v))
            return
        options=[(len(rels[w,z]),z,w) for z in occupied if z not in assigned for w in assigned if (w,z) in rels]
        assert options,'The crossing projection graph of the connected path must be connected.'
        _,z,w=min(options);h=assigned[w]
        for r in rels[w,z]:
            g=tuple(h[r[u]] for u in range(1<<k))
            if not compatible(z,g):continue
            assigned[z]=g;dfs();del assigned[z]
    try:dfs()
    except TimeoutError:status='LIMIT'
    row=dict(base_coordinates=basecoords,block_coordinates=blockcoords,status=status,nodes=nodes,assignments_mod_global=solutions,cube_classes=len(classes),different_images=changed,crossing_edges=edgeinfo);rows.append(row)
    print(basecoords,'nodes',nodes,'assignments',solutions,'classes',len(classes),'changed',changed,status,flush=True)
    if status!='COMPLETE':break
out=dict(status=status,base_size=a.base_size,records=rows,examples=examples,cube_classes=len(allclasses),seconds=time.monotonic()-start,node_limit_per_partition=a.nodes,wall_limit_seconds=a.seconds,resource_gate=gate,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='All independent local cube isometries on each occupied slice, for every completed coordinate partition, normalized by a common global block isometry. Exact pointwise crossing stabilizers and every interslice nonedge are enforced; finite native calculation only.')
(H/'data'/('slices-'+str(a.base_size)+'.json')).write_text(json.dumps(out,indent=2)+'\n')
print('SAVED slices',a.base_size,status,round(out['seconds'],3),'seconds')
