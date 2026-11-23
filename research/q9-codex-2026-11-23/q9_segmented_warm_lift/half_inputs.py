from pathlib import Path
from collections import Counter
import json
D=Path(__file__).resolve().parent
pub=[list(map(int,l.split())) for l in (D/'public191.txt').read_text().splitlines()]
def valid(p):return len(set(p))==len(p) and all(((v^q).bit_count()==1)==(j==i+1) for j,v in enumerate(p) for i,q in enumerate(p[:j]))
def norm(w):
    m={};return ''.join(str(m.setdefault(c,len(m))) for c in w)
def word(p):
    w=''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]));return min(norm(w),norm(w[::-1]))
def audit():
    old={word(z) for z in pub};sets={};counts={};best=None;bestkey=None
    for tag in ['control','blind','mixed']:
        counts[tag]=Counter();cz=set();cross=set();centers=set();both=0
        for l in (D/(tag+'.log')).read_text().splitlines():
            if not l.startswith('W '):continue
            it,k,b,i,n,w,ws,left,right,e,*p=map(int,l.split()[1:]);assert len(p)==e+1 and valid(p)
            original=pub[k][b::2];colour=original[i].bit_count()%2;a=[v for v in p if v.bit_count()%2==colour];assert a[left:left+n]==original[i:i+n] and len(a)==n+left+right
            assert all((x^y).bit_count()==2 for x,y in zip(a,a[1:]));counts[tag][e]+=1;cz.add(word(p));diff=word(p)!=word(pub[k]);centers.add((k,b,i,n));both+=left>0 and right>0
            if e==191 and diff:cross.add(word(p))
            rank=(e,tag=='blind',diff,min(left,right)>=8,-n,min(left,right))
            if bestkey is None or rank>bestkey:bestkey=rank;best=dict(edges=e,path=p,source=tag,run=it,archive=k,parity=b,offset=i,anchors=n,left=left,right=right)
            if tag=='control':continue
            z=[v^colour for v in a];key=(min(z[0],z[-1]),max(z[0],z[-1]),tuple(sorted(z)));sets[key]=z
        counts[tag]=dict(lengths=counts[tag],known191=sum(len(w)==191 and w in old for w in cz),different_from_parent_191_classes=len(cross),distinct_centers_among_witnesses=len(centers),both_wings_nonempty=both,last=(D/(tag+'.log')).read_text().splitlines()[-1])
    with (D/'halfsets.txt').open('w') as f:
        for z in sets.values():print(len(z),*z,file=f)
    with (D/'halfcontrol.txt').open('w') as f:
        for p in pub:
            a=p[:191:2];a=[x^(a[0].bit_count()%2) for x in a];z=a[1:-1];print(len(z),*z,a[0],a[-1],file=f)
    rep=dict(rows=counts,best=best,final_inputs=Counter(map(len,sets.values())))
    if (D/"far_finish.log").exists() and (D/"far_finish.log").stat().st_size:
        positive=[list(map(int,l.split()[1:])) for l in (D/"halfcontrol.log").read_text().splitlines() if l.startswith("FOUND ")]
        assert len(positive)==len(pub) and all(len(p)==191 and valid(p) for p in positive)
        rep["halfcontrol_pairs"]=sum(len(p)*(len(p)-1)//2 for p in positive)
        rep["terminal_logs"]={f:(D/f).read_text().splitlines()[-1] for f in ["halfcontrol.log","finish.log","far_finish.log"]}
    (D/"warm_verified.json").write_text(json.dumps(rep,indent=2)+"\n")
    print(counts,Counter(map(len,sets.values())))
if __name__=='__main__':audit()
