"""Verify the catalogue, labelled cluster copies, coverage counts and the lower witness."""
import hashlib
import json
from collections import Counter
from math import factorial
from pathlib import Path

def decode(s):
    p=[0]
    for d in s:p.append(p[-1] ^ (1<<int(d)))
    return p
def steps(p):
    return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
def norm(s):
    d={}
    return tuple(d.setdefault(c,len(d)) for c in s)
def shape(s):
    return min(norm(s),norm(s[::-1]))
def check(p,d):
    assert len(set(p))==len(p) and all(0<=x<1<<d for x in p)
    assert all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
def fit(arm,bank):
    wanted=steps(arm);sig=norm(wanted)
    for index,w in enumerate(bank):
        for backwards in (False,True):
            donor=w[::-1] if backwards else w
            for t in range(len(donor)-len(wanted)+1):
                seg=donor[t:t+len(wanted)]
                if norm(seg)!=sig:continue
                perm={int(a):int(b) for a,b in zip(seg,wanted)}
                spare=iter(sorted(set(range(8))-set(perm.values())))
                for a in range(8):
                    if a not in perm:perm[a]=next(spare)
                placed=[sum(1<<perm[d] for d in range(8) if x&(1<<d)) for x in decode(donor)]
                shift=arm[0]^placed[t];placed=[x^shift for x in placed]
                assert placed[t:t+len(arm)]==arm;check(placed,8)
                return dict(row=index+1,reverse=backwards,start=t,placed_vertices=placed)
def control(bank):
    for w in Path('q9_three_axis_191.in').read_text().splitlines():
        for axis,count in Counter(w).items():
            if count!=1:continue
            a=int(axis);j=w.index(axis);p=decode(w)
            def lower(x):return ((x>>(a+1))<<a)|(x% (1<<a))
            arms=[[lower(x) for x in p[:j+1]],[lower(x) for x in p[j+1:]]]
            matches=[fit(arm,bank) for arm in arms]
            if all(matches):
                q=arms[0]+[256+x for x in arms[1]];check(q,9);assert len(q)==192
                return dict(edges=191,vertices=q,checked_vertex_pairs=len(q)*(len(q)-1)//2,layers=matches)
    raise ValueError('no lower certificate')
def end(name):
    row=Path(name).read_text().splitlines()[-1].split();assert row[0]=='DONE';return list(map(int,row[1:]))
def run():
    bank=Path('q8_catalogue_96_98.words').read_text().splitlines();counts=Counter(map(len,bank))
    assert len(bank)==len({shape(w) for w in bank})==753
    for w in bank:check(decode(w),8)
    sortbank=sorted(bank,key=len,reverse=True);ids=set();groups=set()
    for line in Path('q8_registered_donor_clusters.txt').read_text().splitlines():
        group,i,*p=map(int,line.split());check(p,8)
        assert i not in ids and shape(steps(p))==shape(sortbank[i]);ids.add(i);groups.add(group)
    assert len(ids)==len(bank)
    att=control(bank);sources=Path('q8_catalogue_96_98.words').read_bytes()
    paircount=len(bank)*(len(bank)+1)//2
    report=dict(donor_lengths=counts,source_sha256=hashlib.sha256(sources).hexdigest(),clusters=len(groups),
        unordered_pairs=paircount,labelled_relative_placements=paircount*256*factorial(8),lower_certificate=att)
    negs={}
    for extra,logs in [(0,['q8_clustered_hosts_192_0.log','q8_clustered_hosts_192_1.log']),(1,['q8_clustered_hosts_plus_one.log']),(2,['q8_clustered_hosts_plus_two_0.log','q8_clustered_hosts_plus_two_1.log'])]:
        rows=[end(name) for name in logs];assert all(r[0]==192 for r in rows) and sum(r[2] for r in rows)==paircount
        surviving=sum(r[4] for r in rows)
        f=Path(['q8_clustered_independent_192.log','q8_clustered_independent_plus_one.log','q8_clustered_independent_plus_two_checked.log'][extra])
        tail=f.read_text().splitlines() if f.exists() else []
        verified=bool(tail) and tail[-1].startswith('DONE')
        if verified:assert end(f)==[192,extra,paircount,surviving,0]
        negs[extra]=dict(surviving_overlap_filter=surviving,solver_nodes=sum(r[5] for r in rows),
                          independent_full_replay=verified)
    report['no_192']=negs
    small=[list(map(int,line.split()[1:])) for line in Path('q8_external_small_check.log').read_text().splitlines()]
    assert len(small)==4 and all(r[0]==e and sum(r[1:])==900 for e,r in enumerate(small))
    ver=Path('q8_external_controls.log').read_text().splitlines()
    assert ver==[f'PASS essential_external_points {e} edges 191' for e in range(4)]
    report['independent_small_instance_checks']=sum(sum(r[1:]) for r in small)
    report['positive_191_required_extra_counts']=list(range(4))
    for e in (195,196):
        tokens=Path(f'q8_catalogue_multicross_{e}.log').read_text().split()
        assert tokens[0]=='NO_JOIN';r=dict(zip(tokens[1::2],map(int,tokens[2::2])))
        n=sum(len(x)+len(y)+1>=e for i,x in enumerate(bank) for y in bank[i:])
        assert r['placements']==n*256*factorial(8) and r['pairs']==n and r['eligible']==0
    Path('q8_catalogue_lifts_verified.json').write_text(json.dumps(report,indent=2)+'\n')
    print(paircount,report['labelled_relative_placements'],negs,att['edges'])
if __name__=='__main__':run()
