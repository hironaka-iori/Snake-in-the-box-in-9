"""Direct witness and geometry replay independent of the C++ search code."""
from pathlib import Path
from collections import Counter,defaultdict
from itertools import permutations,combinations
import json
D=Path(__file__).resolve().parent;R=D.parent
p7=list(permutations(range(7)));p8=list(permutations(range(8)))
def read(fn):return (D/fn).read_text().splitlines()
def summary(fn):
    z=read(fn)[-1].split();assert z[0]=='DONE'
    return dict(zip(z[1::2],map(int,z[2::2])))
def path(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def split(x,a,b):
    other=[k for k in range(9) if k!=a and k!=b]
    return ((x>>a&1)+2*(x>>b&1),sum((x>>k&1)<<j for j,k in enumerate(other)))
def iso(x,p,sh=0):return sh^sum(1<<k for i,k in enumerate(p) if x>>i&1)
def embed(v,om):return (v&((1<<om)-1))|((v>>om)<<(om+1))
def checkpath(p):
    assert len(set(p))==len(p) and max(p)<512 and min(p)>=0
    for i,v in enumerate(p):
        for j in range(i):
            h=(v^p[j]).bit_count();assert h==1 if j==i-1 else h>=2
def signatures(points,n):
    return sorted(sum((((x^points[0])>>k)&1)<<j for j,x in enumerate(points)) for k in range(n))
def ins(fn,withholes=False):
    rs=[]
    for s in read(fn+'.in'):
        i,a,b,*p=map(int,s.split());holes=[]
        if withholes:h=p.pop(0);holes,p=p[:h],p[h:]
        rs.append((i,a,b,holes,p))
    return rs
ar=(R/'q9_gap_generations/prior191.words').read_text().split();arw=(R/'q9_via_q10/monotone_near.words').read_text().split()
mothers=json.loads((D/'target.json').read_text());assert len(mothers)==7
for r in mothers:
    p=path(arw[r['id']]);nonseq=[(i,j,(v^u).bit_length()-1) for j,v in enumerate(p) for i,u in enumerate(p[:j-1] if j else []) if (v^u).bit_count()==1]
    assert len(p)==len(set(p))==193 and set(nonseq)==set(map(tuple,r['chords'])) and set.intersection(*[{i,j} for i,j,d in nonseq])=={96}
cases=ins('target');viable=[]
for i,a,b,_,p in cases:
    assert p==path(arw[i])
    gr=defaultdict(set)
    for x in p:
        s,z=split(x,a,b);gr[s].add(z)
    if max(sum((v^1<<k) in g for k in range(7)) for g in gr.values() for v in g)<=2:viable.append([i,a,b])
assert len(cases)==252 and len(viable)==11
out={'seed_rows_zero_based':[s['id'] for s in mothers],'viable_cuts':viable};batches={}
def geomfile(name,inputname,typ):
    ls=read(name+'.log');rs=ins(inputname,withholes=(typ=='orderedhole'));allrows=defaultdict(list)
    for i,a,b,h,p in rs:allrows[i,a,b].append((h,p))
    hits=0;examples=[]
    for pos,rec in enumerate(ls):
        fields=rec.split()
        if fields[0]!='HIT':continue
        i,a,b=map(int,fields[1:4]);rows=allrows[i,a,b];q=fields[4:];h=[]
        if typ=='orderedhole':
            n=int(q[0]);h=list(map(int,q[1:n+1]));q=q[n+1:];p=next(p for holes,p in rows if holes==h)
        else:p=rows[0][1]
        if typ in ('ordered','orderedhole'):
            v=list(map(int,q));assert len(v)==len(p)
            for g in range(4):
                src=[];dest=[]
                for j,x in enumerate(p):
                    k,y=split(x,a,b)
                    if k==g and j not in h:src.append(y);dest.append(v[j])
                assert sorted([0,0]+signatures(src,7))==signatures(dest,9)
        else:
            lay=list(map(int,q[0]));coords=list(map(int,q[1:7]));q=q[7:];A,B,C,E=lay
            lm,lt,cm,ct,rm,rt=coords;extra=[]
            if typ=='repair':
                sz=int(q[0]);extra=list(map(int,q[1:sz+1]));q=q[sz+1:]
            if typ=='overlap':
                _tag,_id,_a,_b,ox,oy=ls[pos+1].split();assert _tag=='SUPPORT' and int(_id)==i;ox=int(ox);oy=int(oy)
            transformed=[]
            for x in p:
                g,w=split(x,a,b)
                if typ=='parallel':
                    z=w if g==A else iso(w,p7[lm],lt)+128 if g==B else iso(w,p7[cm],ct)+384 if g==C else iso(w,p7[rm],rt)+256
                elif g==A:z=w
                elif g==B:z=embed(iso(w,p7[lm]),ox)^lt if typ=='overlap' else (128+iso(w,p7[lm],lt))
                else:
                    v=w if g==C else (embed(iso(w,p7[cm]),oy)^ct if typ=='overlap' else 128+iso(w,p7[cm],ct))
                    z=256+iso(v,p8[rm],rt)
                transformed.append(z)
            v=list(map(int,q));assert len(v)==len(transformed)+len(extra) and set(v)==set(transformed)|set(extra)
        checkpath(v);hits+=1
        if len(examples)<1:examples.append(dict(file=name+'.log',line=pos+1,source=i,cut=[a,b],vertices=len(v),pairs=len(v)*(len(v)-1)//2,first=v[0],last=v[-1]))
    batches[name]=dict(checked=hits,examples=examples,run=summary(name+'.log'))
for n,s,t in [('faces_control','control','parallel'),('partition_control','adaptive_control','partition'),('parallel_adaptive','adaptive_control','parallel'),('overlap_control','adaptive_control','overlap'),('intersects_control','intersects_control','overlap'),('ordered_control','control','ordered'),('ordered_adaptive','adaptive_control','ordered'),('holes1_control','adaptive_control_holes1','repair'),('ordered_holes_control','adaptive_control_orderholes2','orderedhole')]:
    geomfile(n,s,t)
out['positive_replay']=batches
sig=[]
for ln in read('all_signatures.tsv'):
    i,a,b,A,B,pi,tx,dm,port,isol=map(int,ln.split());p=path(arw[i]);v=[]
    for x in p:
        g,z=split(x,a,b)
        if g==A:v.append(z)
        if g==B:v.append(128+iso(z,p7[pi],tx))
    S=set(v);deg={x:sum(x^1<<k in S for k in range(8)) for x in S}
    assert max(deg.values())<=2 and sum(2-v for v in deg.values())==dm and sum(d<2 for d in deg.values())==port and sum(d==0 for d in deg.values())==isol
    left=S.copy()
    while left:
        part=[left.pop()]
        for x in part:
            hits={x^1<<k for k in range(8)}&left;left-=hits;part.extend(hits)
        assert sum(deg[x] for x in part)==2*(len(part)-1)
    sig.append((i,a,b,A,B))
assert len(sig)==92
intct=sum(1 for u,v in combinations(sig,2) if u[:3]==v[:3] and not(set(u[3:])&set(v[3:])))
assert intct==22
for filename in ('faces_target','ordered_target','partition_target','overlap_target','pair_screen','independent_intersections','independent_ports','all_half','forest_join','direct_forest','holes1','holes2','strict_holes1','strict_holes2','connector1','connector2','connector3','connector4','forest_positive'):
    out[filename]=summary(filename+'.log')
assert out['forest_join']['interhalf_relative_isometries']==out['direct_forest']['interhalf_relative_isometries']==intct*40320*256
assert out['independent_intersections']['ambient_intersection_placements']==out['pair_screen']['intersecting_face_isometries']==4811304960
assert out['forest_join']['maximum_degree_two']==out['direct_forest']['maximum_degree_two']==0
assert not read('all_forests.tsv') and not read('overlaps.tsv') and not read('independently_possible.tsv')
out['three_168_edge_controls_form_geometrically_intersecting_faces']=sum(s.startswith('SUPPORT') and any(int(d)!=7 for d in s.split()[-2:]) for s in read('intersects_control.log'))
out['positive_minimum_components']=min(int(l.split()[10]) for l in read('positive_forests.tsv'))
(D/'audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('independent pair placements',out['independent_intersections']['ambient_intersection_placements'],'half forests and complementary pairs',len(sig),intct,'full degree-compatible placements',out['direct_forest']['maximum_degree_two'],'positive batches', {k:v['checked'] for k,v in batches.items()})
