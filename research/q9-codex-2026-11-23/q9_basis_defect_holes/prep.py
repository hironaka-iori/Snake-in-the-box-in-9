from pathlib import Path
from itertools import combinations
from collections import Counter
import json, random
D=Path(__file__).resolve().parent;R=D.parent
def path(w):
    q=[0]
    for a in w:q.append(q[-1]^1<<int(a))
    return q
def edges(p):return {tuple((i,j)) for i,x in enumerate(p) for j in range(i+2,len(p)) if (x^p[j]).bit_count()==1}
def norm(w):
    def key(z):
        m={};return ''.join(str(m.setdefault(a,len(m))) for a in z)
    return min(key(w),key(w[::-1]))
def geom(p):
    assert len(p)==len(set(p))==193 and all((u^v).bit_count()==1 for u,v in zip(p,p[1:]))
    return norm(''.join(str((u^v).bit_length()-1) for u,v in zip(p,p[1:])))
def write(tag,rows):
    (D/(tag+'.txt')).write_text(''.join('points '+' '.join(map(str,r['points']))+'\n' for r in rows));(D/(tag+'.jsonl')).write_text(''.join(json.dumps({k:v for k,v in r.items() if k!='points'},separators=(',',':'))+'\n' for r in rows))
def main():
    bank={};sources=[R/'q8_single_cross_192_onechord_paths.txt',R/'q8_complete_single_cross_near_192.txt',R/'q9_via_q10/monotone_near.words',R/'q9_via_q10/near_registered.words',R/'q9_via_q10/all_near_registered.words']
    for f in sources:
        for row,l in enumerate(f.read_text().splitlines()):
            if f.suffix=='.words':
                if len(l)!=192:continue
                p=path(l)
            else:p=list(map(int,l.split()))
            if len(set(p))!=193:continue
            err=edges(p)
            if len(err) not in (1,2):continue
            k=geom(p);bank.setdefault(k,[]).append([str(f.relative_to(R)),row])
    select=[];near=[];chosen=set();tags=Counter()
    for seed,(word,refs) in enumerate(sorted(bank.items(),key=lambda y:(len(edges(path(y[0]))),y[0]))):
        p=path(word);e=sorted(edges(p));tips=sorted(set(sum((list(t) for t in e),[])))
        # Each edge of the defect set must lose an endpoint; freely choose additional vertices adjoining a defect in the original sequence.
        close=sorted({j for t in tips for j in range(max(0,t-2),min(193,t+3))}|{0,192})
        for h in (1,2,3):
            for rm in combinations(close,h):
                if not all(set(rm)&set(pair) for pair in e):continue
                x=dict(seed=seed,chords=e,rm=rm,refs=refs,word=word,points=[v for i,v in enumerate(p) if i not in rm]);kind=('tips' if set(rm)<=set(tips) else 'neighborhood');tags[(len(e),h,kind)]+=1
                (select if kind=='tips' else near).append(x)
    select.sort(key=lambda r:(len(r['rm']),len(r['chords']),r['seed'],r['rm']))
    random.Random(31897).shuffle(near);write('endpoints',select);write('local',near)
    seeds=[dict(word=w,refs=v,chords=sorted(edges(path(w)))) for w,v in bank.items()];(D/'source_seeds.json').write_text(json.dumps(seeds))
    rs=random.Random(58117);true=(R/'q9_gap_generations/prior191.words').read_text().split();pos=[]
    for h in (1,2,3):
        for kind in (0,1):
            q=path(true[h+2*kind]);basis=[];span={0}
            while len(basis)<9:
                x=rs.randrange(1,512)
                if x in span or x.bit_count()<2:continue
                basis.append(x);span|={v^x for v in span}
            shift=rs.randrange(512);mapping=[0]
            for x in basis:mapping+= [v^x for v in mapping]
            r=[mapping[v]^shift for v in q];rm=sorted(rs.sample(range(1,191),h)) if not kind else list(range(0,h));v=[a for j,a in enumerate(r) if j not in rm];rs.shuffle(v)
            pos.append(dict(points=v,rm=rm,index=h+2*kind,basis=basis,shift=shift))
    write('positive',pos);print(json.dumps(dict(seeds=Counter(len(edges(path(w))) for w in bank),endpoints=len(select),local=len(near),by={str(k):v for k,v in tags.items()})))
if __name__=='__main__':main()
