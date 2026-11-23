"""Independent source, group-schedule, and pairwise cube geometry replay."""
from pathlib import Path
from itertools import combinations, permutations
from collections import Counter
from functools import lru_cache
import json
D = Path(__file__).resolve().parent
def rows(name): return [json.loads(s) for s in (D/(name+'.jsonl')).read_text().splitlines()]
def vis(w):
    p=[0]
    for c in w: p.append(p[-1]^(1<<int(c)))
    return p
nb=[[i^(1<<j) for j in range(9)] for i in range(512)]
@lru_cache(maxsize=35000)
def flaws(w):
    v=vis(w); f=Counter(v)
    dup=sum(n*(n-1)//2 for n in f.values())
    return dup+sum(f[x]*f[y] for x in f for y in nb[x] if y>x)-len(w)
@lru_cache(maxsize=2000)
def allpairs(w):
    vs=vis(w)
    assert len(set(vs))==len(vs)
    assert all((x^y).bit_count()==1 if j==i+1 else (x^y).bit_count()>1 for i,x in enumerate(vs) for j,y in enumerate(vs) if j>i)
def norm(w):
    return w.translate(str.maketrans(''.join(dict.fromkeys(w)), '012345678'[:len(set(w))]))
def canon(w): return min(norm(w),norm(w[::-1]))
def orientation(z,r): return z[::-1] if r else z
def labels(w,g): return w.translate(str.maketrans('012345678',g))
def tracks(w,g): return tuple(''.join(c for c in w if g[int(c)]==str(k)) for k in range(3))
def validgroup(g): assert Counter(g)=={'0':3,'1':3,'2':3}
def checkoutput(w,z,g):
    assert tracks(w,g)==tracks(z,g)
    if not flaws(z): allpairs(z)
bank=(D.parent/'q9_gap_generations/prior191.words').read_text().split()
for w in bank: assert len(w)==191;allpairs(w)
idx={canon(w):i for i,w in enumerate(bank)}
assert len(idx)==len(bank)==131
near=(D.parent/'q9_three_axis.in').read_text().split()
counts=Counter();out={}; examples={}
for seed in (317123,881937,975413):
    for typ in ('target','control'):
        source=rows(f'{typ}_{seed}')
        for r in source:
            w=orientation(bank[r['a']],r['rev']);g=''.join(map(str,r['groups']));h=''.join(map(str,r['donor_groups']))
            validgroup(g);validgroup(h);a,b=r['patches'];assert a['mp']!=b['mp'] and a['at']+a['n']<=b['at']
            for p in (b,a):
                s=orientation(bank[p['b']],p['rev'])[p['j']:p['j']+p['L']];m=p['mp']
                assert p['b']!=r['a'] and ''.join(sorted(m))=='012345678' and all(h[i]==g[int(m[i])] for i in range(9))
                s=s.translate(str.maketrans('012345678',m));assert s==p['piece']
                i,n=p['at'],p['n'];u=w[i:i+n];assert labels(u,g)!=labels(s,g)
                assert (tracks(u,g)==tracks(s,g))==(typ=='control')
                w=w[:i]+s+w[i+n:]
            assert r['word']==w and len(w)==191+int(typ=='target') and flaws(w)==r['defects']
            counts[typ+'_rows']+=1
            if a['b']==b['b']:counts[typ+'_same_B']+=1
out['two_windows']=dict(counts)
archive_labels=set()
for aa in combinations(range(9),3):
    if 0 not in aa:continue
    unused=set(range(9))-set(aa)
    for bb in combinations(sorted(unused),3):
        if min(unused) not in bb:continue
        g=''.join('0' if k in aa else '1' if k in bb else '2' for k in range(9))
        for w in bank:archive_labels.add(canon(labels(w,g)))
rawlabelset={p.translate(str.maketrans('012', ''.join(perm))) for c in archive_labels for p in (c,c[::-1]) for perm in permutations('012')}
co=rows('complete_control');tg=rows('complete_target')
for mode,ds in [('complete_control',co),('complete_target',tg)]:
    result=Counter()
    for r in ds:
        g,w=r['groups'],r['raw'];validgroup(g);p=r['providers'];t=r['template_word']
        assert t==(bank if mode=='complete_control' else near)[r['template']]
        assert len(set(z['b'] for z in p))>=2
        for z,u,tt in zip(p,tracks(w,g),tracks(t,g)):
            q=orientation(bank[z['b']],z['rev'])
            q=''.join(x for x in q if x in z['axes']).translate(str.maketrans(z['axes'],z['mapping']))
            assert u==q==z['track'] and (u!=tt)==z['altered']
            if mode=='complete_control':assert z['b']!=r['template']
        assert flaws(w)==r['defects']>0
        l=labels(w,g)
        if mode=='complete_control':assert l not in rawlabelset
        else:
            assert l==labels(t,g)
            single=any(l[:i]+l[i+1:] in rawlabelset for i in range(len(l)))
            assert single==r['single_insert']
            result['strict_multiple_events']+=not single
        result['changed_tracks']+=any(z['altered'] for z in p)
        result['rows']+=1
    out[mode]=dict(result)
out['canonical_group_schedules']=len(archive_labels)
knownnear={canon(w) for w in near}
near1={};trim_ids=set();seamrows=rows('seam_damage');double_control=rows('control_975413')
def inputrows(x):return [tuple(s.split()[:2]) for s in (D/(x+'.in')).read_text().splitlines()]
path_map={'ctrl':'control_317123','two_control':'control_975413','first':'target_317123','tip_full':'target_881937','two_full':'target_975413','trim_left':'target_881937_left','trim_right':'target_881937_right','complete_ctrl':'complete_control','complete_full':'complete_target','moves_ctrl':'complete_control','moves_full':'complete_target','moves_left':'complete_target','moves_right':'complete_target','pair_control':'pair_control','pair_target':'pair_target','seam_damage':'seam_damage','seam_replay':'seam_damage'}
out['replay']={}
for name,src in path_map.items():
    inp=inputrows(src);zcount=Counter();ds=set()
    for line in (D/(name+'.paths')).read_text().splitlines():
        fields=line.split();i=int(fields[0]);z=fields[-1];w,g=inp[i]
        if name=='moves_left':w=w[1:]
        if name=='moves_right':w=w[:-1]
        checkoutput(w,z,g);a,b=flaws(w),flaws(z)
        if len(fields)==4:assert [int(t) for t in fields[1:3]]==[a,b]
        else:assert not b
        zcount['lines']+=1
        if not b:
            ds.add(canon(z));zcount['valid']+=1;zcount['started_damaged']+=a>0
            if name in ('moves_left','moves_right'):
                cid=idx.get(canon(z),-1);trim_ids.add(cid)
                zcount['distinct_from_all_providers']+=cid not in [q['b'] for q in tg[i]['providers']]
            if name in ('seam_damage','seam_replay'):
                se=seamrows[i]; m=se['seams'];lv=labels(w,g);lz=labels(z,g)
                patches=double_control[se['parent_control']]['patches'];nwin=len({k for t in m for k,patch in enumerate(patches) if t in (patch['at'],patch['at']+patch['L'])});zcount['seams_from_'+str(nwin)+'_windows']+=1
                n=sum(Counter(lv[:t])!=Counter(lz[:t]) for t in m);zcount['changed_'+str(n)+'_seams']+=1
                if n==2 and 'double_seam' not in examples:examples['double_seam']=dict(row=i,parent_control=se['parent_control'],seams=m,groups=g,raw=w,recovered=z,archive_class=idx.get(canon(z)),defects_before=a)
        elif b==1 and name=='moves_full' and len(set(vis(z)))==193:
            allnew=canon(z) not in knownnear;near1[canon(z)]=dict(row=i,raw=z,outside_input=allnew)
    zcount['classes']=len(ds);out['replay'][name]=dict(zcount)
out['trimmed_191_archive_classes']=sorted(trim_ids)
out['retimed_one_chord_classes']=len(near1)
out['retimed_one_chord_classes_outside_input']=sum(z['outside_input'] for z in near1.values())
(D/'one_chord_retimed.jsonl').write_text(''.join(json.dumps(e)+'\n' for e in near1.values()))
sat=[('complete_radius1','complete_target',1),('sat_ctrl','control_975413',2),('sat_tip2','target_881937',2),('sat_tip3','target_881937',3),('sat_two','target_975413',2),('complete_sat2','complete_target',2),('complete_sat4','complete_target',4),('complete_cadical','complete_target',2),('sat_seam_control','seam_damage',2)]
out['sat']={};exclusions=set()
for name,src,rad in sat:
    ds=rows(name); inp=inputrows(src)
    for q in ds:
        w,g=inp[q['i']];z=q['word']
        if not z: continue
        checkoutput(w,z,g);assert flaws(z)==0
        a=labels(w,g);b=labels(z,g);u=[0,0,0]
        for x,y in zip(a,b):
            u[int(x)]+=1;u[int(y)]-=1;assert max(map(abs,u))<=rad
    out['sat'][name]=dict(Counter(q['status'] for q in ds))
    if name in ('complete_sat2','complete_cadical'):exclusions.update(q['i'] for q in ds if q['status'] in ('UNSAT','EMPTY'))
out['radius2_distinct_excluded_rows']=len(exclusions)
(D/'seam_example.json').write_text(json.dumps(examples,indent=2)+'\n')
(D/'audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
