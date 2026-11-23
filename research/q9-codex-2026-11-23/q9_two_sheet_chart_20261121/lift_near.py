"""Turn Q9 chorded walks into genuine Q10 paths, then search other charts."""
from pathlib import Path
from collections import Counter
from pysat.solvers import Minicard
from harvest import canon,valid
from control import tab
import sys,random,json
D=Path(__file__).resolve().parent
def lift(p,lookup,chords,rng,sw):
    inverse=[0]*512
    for x,y in enumerate(lookup):inverse[y]=x
    inv=[inverse[x] for x in p];idx={v:i for i,v in enumerate(p)};clauses=[];switches=[];possible=0
    n=len(p)
    for j in range(n-1):
        ab=(p[j]==inv[j+1]);ba=(inv[j]==p[j+1]);a,b=j+1,j+2
        if not ab:clauses.append([a,-b])
        if not ba:clauses.append([-a,b])
        if not ab and not ba:continue
        s=n+1+j;switches.append(s)
        clauses += [[-a,-b,-s],[a,b,-s],[a,-b,s],[-a,b,s]]
    if len(switches)<sw:return
    for b,v in enumerate(inv):
        a=idx.get(v)
        if a is not None and abs(a-b)>1:clauses.append([a+1,-b-1])
    for a,b in chords:clauses.extend([[a+1,b+1],[-a-1,-b-1]])
    with Minicard(bootstrap_with=clauses) as sat:
        sat.add_atmost([-x for x in switches],len(switches)-sw)
        sat.set_phases([s if rng.randrange(2) else -s for s in switches])
        if not sat.solve():return
        model=set(sat.get_model())
    tags=[int(i+1 in model) for i in range(n)]
    q=[x+512 if t else v for v,x,t in zip(p,inv,tags)]
    if len({(x^y).bit_length()-1 for x,y in zip(q,q[1:])})!=10:return
    valid(q,10);return q,sum(x!=y for x,y in zip(tags,tags[1:]))
def main():
    seed,take,tries=map(int,sys.argv[1:]);rng=random.Random(seed);bank=(D.parent/'q9_three_axis.in').read_text().split();ids=list(range(len(bank)));rng.shuffle(ids);seen=set();meta=[];full=[];extended=[];em=[]
    for i in ids[:take]:
        p=[0]
        for c in bank[i]:p.append(p[-1]^1<<int(c))
        idx={x:j for j,x in enumerate(p)}
        ch=[(j,idx[u]) for j,x in enumerate(p) for k in range(9) if (u:=x^1<<k) in idx and idx[u]>j+1]
        assert len(p)==len(idx)==193 and 1<=len(ch)<=2
        for branch in (0,1):
            for _ in range(tries):
                mp=list(range(9));t=rng.randrange(192)
                if branch:
                    ds=rng.sample(range(9),rng.choice([2,2,3,4]))
                    for k in ds[1:]:mp[ds[0]],mp[k]=mp[k],mp[ds[0]]
                off=p[t+1]^tab(mp,0)[p[t]]
                lookup=tab(mp,off);v=lift(p,lookup,ch,rng,3+rng.randrange(5))
                if not v:continue
                q,sw=v;key=canon([(a^b).bit_length()-1 for a,b in zip(q,q[1:])])
                if key in seen:continue
                seen.add(key);full.append(q);meta.append(dict(source=i,chart=mp,offset=off,switches=sw,chords=ch))
                e=q[:];occ=set(e)
                while len(e)<197:
                    opts=[]
                    for side,u in enumerate((e[0],e[-1])):
                        for k in range(10):
                            x=u^1<<k
                            if x not in occ and all((x^1<<d) not in occ or (x^1<<d)==u for d in range(10)):opts.append((side,x))
                    if not opts:break
                    side,x=rng.choice(opts);occ.add(x)
                    if side:e.append(x)
                    else:e.insert(0,x)
                if len(e)==197:valid(e,10);extended.append(e);em.append(len(meta)-1)
                break
    (D/f'near_{seed}.pts').write_text(''.join('10 '+' '.join(map(str,p))+'\n' for p in full))
    (D/f'near_{seed}.json').write_text(json.dumps(meta,separators=(',',':'))+'\n')
    (D/f'extend_{seed}.pts').write_text(''.join('10 '+' '.join(map(str,p))+'\n' for p in extended))
    (D/f'extend_{seed}.json').write_text(json.dumps(em)+'\n')
    print('source_rows',take,'lifts',len(full),'distinct_sources',len({m['source'] for m in meta}),'by_source_chords',dict(Counter(len(m['chords']) for m in meta)),'nonidentity',sum(m['chart']!=list(range(9)) for m in meta),'extended_to_196',len(extended))
if __name__=='__main__':main()
