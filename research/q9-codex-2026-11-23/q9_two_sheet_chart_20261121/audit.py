"""Independent reconstruction and direct pairwise verification of all returned Q9 paths."""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import json
D=Path(__file__).resolve().parent;R=D.parent
def pts(f):return [list(map(int,s.split()))[1:] for s in f.read_text().splitlines()]
def read(f):return json.loads((D/f).read_text())
def canonical(z):
    def one(q):
        mp={};return bytes(mp.setdefault(c,len(mp)) for c in q)
    return min(one(z),one(z[::-1]))
def edges(p):return [(a^b).bit_length()-1 for a,b in zip(p,p[1:])]
def walk(w):
    out=[0]
    for k in w:out.append(out[-1]^1<<k)
    return out
def geom(p,n,allpairs=False):
    assert len(p)==len(set(p)) and all(0<=x<1<<n for x in p)
    if allpairs:
        for j,v in enumerate(p):
            for k in range(j):assert ((v^p[k]).bit_count()==1)==(k+1==j)
    else:
        older=set()
        for j,v in enumerate(p):
            assert {v^1<<k for k in range(n)}&older==({p[j-1]} if j else set())
            older.add(v)
def iso(x,perm,off):
    return off ^ sum(1<<int(j) for i,j in enumerate(perm) if x>>i&1)
def chart(q,axis,side,mp,off):
    low=(1<<axis)-1
    z=[(x&low)|((x>>(axis+1))<<axis) for x in q]
    return [x if (v>>axis)&1==side else iso(x,mp,off) for v,x in zip(q,z)]
def stats(log):
    lines=(D/log).read_text().splitlines();fields=lines[-1].split();assert fields[0]=='DONE'
    return dict(zip(fields[1::2],map(int,fields[2::2])))
files={'goal':R/'q9_three_seam_folds/q10_12.txt','sub':D/'subfacets.pts','children':D/'children.pts','near':D/'near_573291.pts','near_extend':D/'extend_573291.pts','control':D/'controls.pts'}
banks={k:pts(v) for k,v in files.items()};out={'sources':{},'targets':{},'independent':{},'witnesses':{}}
for k,ds in banks.items():
    shape=set()
    for p in ds:geom(p,10,k=='goal');e=edges(p);assert len(set(e))==10;shape.add(canonical(e))
    out['sources'][k]={'rows':len(ds),'distinct_whole_path_shapes':len(shape)}
# Verify all new subfacet donors against their declared higher-dimensional source.
refs={}
for z,q in zip(read('subfacets.json'),banks['sub'],strict=True):
    name=z['file']
    if name not in refs:refs[name]=pts(R/'q9_via_q10'/name)
    src=refs[name][z['row']][z['start']:z['stop']+1]
    assert canonical(edges(src))==bytes(edges(q))
archive=[list(map(int,w)) for w in (R/'q9_gap_generations/prior191.words').read_text().split()]
idx={canonical(z):i for i,z in enumerate(archive)}
switches=[];samples=[];known_classes=set()
for i,(z,q) in enumerate(zip(read('controls.json'),banks['control'],strict=True)):
    w=chart(q,9,0,z['requested_permutation'],z['requested_offset']);assert edges(w)==archive[z['archive_id']];geom(w,9,True)
    count=sum((v^u)==512 for v,u in zip(q,q[1:]));assert count==z['switches'];switches.append(count)
    for k in range(9):
        res=chart(q,9,0,range(9),1<<k)
        try:geom(res,9,True)
        except AssertionError:pass
        else:raise AssertionError('translation-only control unexpectedly succeeded')
nearwd=[list(map(int,w)) for w in (R/'q9_three_axis.in').read_text().split()]
for z,q in zip(read('near_573291.json'),banks['near'],strict=True):
    p=chart(q,9,0,z['chart'],z['offset']);assert p==walk(nearwd[z['source']]);geom(q,10)
    assert len(p)==len(set(p))==193
    ix={v:i for i,v in enumerate(p)}
    bad={(i,ix[u]) for i,v in enumerate(p) for k in range(9) if (u:=v^1<<k) in ix and ix[u]>i+1}
    assert bad==set(map(tuple,z['chords']))
for i,e in zip(read('extend_573291.json'),banks['near_extend'],strict=True):
    q=banks['near'][i];assert any(e[j:j+len(q)]==q for j in range(len(e)-len(q)+1))
jobs={'goal':[190,191,192,195,196],'sub':[191,192,195,196],'children':[191,192,195,196],'near':[192],'near_extend':[192,195,196],'control':[191]}
keys={}
for name,ns in jobs.items():
    for g in ns:
        k=name+str(g);f=(k if name!='control' else 'controls')+'.log';ss=stats(f);ds=banks[name];n=sum(max(0,len(p)-g) for p in ds)*(1 if name=='control' else 10)
        assert ss['axis_windows']==n==ss['pruned_windows']+ss['hits'];seen=set()
        for line in (D/f).read_text().splitlines()[:-1]:
            tag,row,a,l,h,side,off,perm,w=line.split();row,a,l,h,side,off=map(int,(row,a,l,h,side,off))
            assert tag=='HIT' and h-l==g and sorted(perm)==list('012345678')
            q=ds[row][l:h+1];p=chart(q,a,side,perm,off);geom(p,9,True);assert edges(p)==list(map(int,w))
            seen.add((row,a,l,g));sw=sum((x^y)==1<<a for x,y in zip(q,q[1:]))
            if name=='control':
                assert sw>=7 and perm!='012345678';samples.append(dict(row=row,changes=sw,length=g,permutation=perm,offset=off,source_side=side,first=p[0],last=p[-1],all_pairs=len(p)*(len(p)-1)//2))
            if name=='children' and g==191:known_classes.add(idx.get(canonical(edges(p)),-1))
        assert len(seen)==ss['hits'];keys[k]=seen
        out['targets'][k]=dict(axis_windows=n,valid=ss['hits'],rows=len(ds))
for g in [190,191,192,195,196]:
    f=f'independent{g}.log';s=stats(f);seen={tuple(map(int,z.split()[1:])) for z in (D/f).read_text().splitlines()[:-1]}
    assert seen==keys['goal'+str(g)] and s['windows']==out['targets']['goal'+str(g)]['axis_windows'];out['independent'][str(g)]=s
s=stats('independent_control.log');assert s['hits']==16
ss=stats('singleton192.log');assert ss['hits']==0 and ss['geometric_core_tests']==22560
out['control_switch_counts']=dict(Counter(switches));out['children_191_archive_classes']=sorted(known_classes);out['independent_positive']=s
out['totals']={str(g):sum(v['axis_windows'] for k,v in out['targets'].items() if k.endswith(str(g)) and not k.startswith('control')) for g in (192,195,196)}
out['witnesses']['control']=samples[0];out['all_190_hit_starts']=sorted({l for _,_,l,_ in keys['goal190']})
(D/'audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
