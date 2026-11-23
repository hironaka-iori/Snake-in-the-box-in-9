"""Replay raw geometry, every complete sibling, and every recovered 191 path."""
from pathlib import Path
from collections import Counter,defaultdict
from functools import lru_cache
import json
D=Path(__file__).resolve().parent
def rows(name):return [json.loads(s) for s in (D/name).read_text().splitlines()]
def points(w):
    v=0;p=[v]
    for c in w:v^=1<<int(c);p.append(v)
    return p
def word(p):return ''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]))
def canon(w):
    def one(s):return s.translate(str.maketrans(''.join(dict.fromkeys(s)),'012345678'[:len(set(s))]))
    return min(one(w),one(w[::-1]))
nb=[sum(1<<(v^1<<k) for k in range(9)) for v in range(512)]
def quick(p):
    used=extra=0
    for i,v in enumerate(p):
        assert 0<=v<512 and not used>>v&1
        extra+=(nb[v]&used).bit_count()-int(i>0);used|=1<<v
    return extra
@lru_cache(maxsize=4000)
def pairwise(p):
    assert len(p)==len(set(p))==192
    adj=0
    for j,v in enumerate(p):
        for i in range(j):
            d=(v^p[i]).bit_count()
            if j==i+1:assert d==1;adj+=1
            else:assert d>1
    return adj==191
archive=(D.parent/'q9_gap_generations/prior191.words').read_text().split()
classes={canon(w):i for i,w in enumerate(archive)}
source=(D.parent/'q9_three_axis.in').read_text().split()
for w in archive:assert pairwise(tuple(points(w)))
out={};summary=Counter();example=None;allclasses=set();pool_winners=set();ctrlsingle=defaultdict(list)
for fn in ('control_tight','control_single','batch_loose','iso_control','iso_target','iso_rest','retry','near191a','near191b','free192a','offspring_a','offspring_b'):
    rs=rows(fn+'.jsonl');out[fn]=dict(Counter(q['status'] for q in rs))
    for q in rs:
        if q['path']:assert pairwise(tuple(q['path']))
        if fn=='control_single':ctrlsingle[q['src']].append(q['status'])
for r in rows('control.pools'):
    p=r['raw'];assert len(r['changed'])==2 and quick(p)==2
    known=points(archive[r['src']])
    assert {i for i,(a,b) in enumerate(zip(p,known)) if a!=b}==set(r['changed'])
for r in rows('control_tight.jsonl'):
    if r['path'] and all(s=='UNSAT' for s in ctrlsingle[r['src']]):pool_winners.add(r['src'])
summary['route_controls_whose_single_alternatives_all_unsat']=len(pool_winners)
isotypes=[('control','iso_control',None),('target','iso_target','near191a'),('rest','iso_rest','near191b')]
for typ,st,nfile in isotypes:
    seeds={}
    for s in (D/(typ+'.seeds')).read_text().splitlines():
        id_,a,b,c,d,w=s.split();id_,a,b,c,d=map(int,(id_,a,b,c,d));p=points(w);seeds[id_]=(w,p,(a,b,c,d));assert quick(p)==2 and 0<a<b<len(p)-1 and 0<c<d<len(p)-1 and (p[a]^p[b]).bit_count()==(p[c]^p[d]).bit_count()==1
        if typ!='control':assert w==source[id_]
    alts=defaultdict(list);nc=0
    for line in (D/(typ+'.isos')).read_text().splitlines():
        id_,cost,repair,lo,hi,rev,mp,n,*tokens=line.split();id_,cost,repair,lo,hi,rev,n=map(int,(id_,cost,repair,lo,hi,rev,n))
        assert len(tokens)==n*2 and ''.join(sorted(mp))=='012345678'
        add=frozenset(map(int,tokens[:n]));remove=frozenset(map(int,tokens[n:]));w,p,ch=seeds[id_]
        piece=w[lo:hi].translate(str.maketrans('012345678',mp));piece=piece[::-1] if rev else piece
        q=points(w[:lo]+piece+w[hi:]);assert quick(q)==cost and len(p)==len(q)
        s1=set(p);s2=set(q);assert s2-s1==add and s1-s2==remove
        x,y,t,u=ch;assert int((q[x]^q[y]).bit_count()>1)+2*int((q[t]^q[u]).bit_count()>1)==repair
        alts[id_].append((add,remove));nc+=1
    out[typ+'_complete_siblings_checked']=nc
    for r in rows(st+'.jsonl'):
        if r['path']:
            p=seeds[r['src']][1];ss=set(p);aa=alts[r['src']];assert set(r['path'])<=ss|set().union(*(aa[j][0] for j in r['picks']))
    if nfile:
        for ix,r in enumerate(rows(nfile+'.jsonl'),1):
            p=r['path']
            if not p:continue
            id_=r['src'];base=set(seeds[id_][1]);growth=set(p)-base;aa=alts[id_]
            assert set(p)<=base|set().union(*(a for a,b in aa))
            require_many=not any(growth<=a for a,b in aa)
            summary['actual_191_from_dual_internal']+=1;summary['actual_191_needing_multiple_siblings']+=require_many
            k=canon(word(p));allclasses.add(k);summary['actual_191_outside_bank']+=k not in classes
            if require_many and example is None:
                example={'source_file':nfile+'.jsonl','one_based_line':ix,'near_path_source':'q9_three_axis.in','near_path_one_based_line':id_+1,'original_chord_indices':seeds[id_][2],'alternative_file':typ+'.isos','available_siblings':len(aa),'new_vertices_over_near_path':sorted(growth),'largest_count_of_these_new_vertices_in_a_single_sibling':max(len(a&growth) for a,b in aa),'known_191_row_zero_based':classes.get(k),'vertices':p,'pairwise_checks':18336,'nonconsecutive_distance_one':0}
summary['actual_191_distinct_classes']=len(allclasses);out['positive_summary']=summary
near={canon(w) for w in source};mix=[]
for fn in ('combined_target.tsv','combined_rest.tsv'):
    for ln in (D/fn).read_text().splitlines():
        cost,src,i,j,w=ln.split();assert len(w)==192 and quick(points(w))==int(cost)==1;mix.append(canon(w))
out['direct_two_sibling_one_chord']={'rows':len(mix),'classes':len(set(mix)),'outside_original_input':len(set(mix)-near)}
(D/'checked_example.json').write_text(json.dumps(example,indent=2)+'\n')
(D/'audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
