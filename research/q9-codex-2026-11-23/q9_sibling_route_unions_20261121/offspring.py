"""Recombine frontier changes of an actual 191-edge child with its mother's alternatives."""
from iso_solve import load
from sat import solve
from build import D,N,B,mask
from collections import defaultdict
import json,random,sys
def tails(p,seed):
    rng=random.Random(seed)
    bank=[];seen=set();orig=set(p)
    for rev in range(2):
        original=p[::-1] if rev else p
        for cut in (0,2,4,6,8,11,14):
            old=original[:len(p)-cut];F=set(old);tip=old[-1];target=cut+1
            ne={x:set(N[x])&F for x in range(512) if x not in F}
            allowed=mask(ne);seq=[];nodes=0;hits=0;order=list(range(9));rng.shuffle(order)
            def walk(x,fmask,cost,bads):
                nonlocal nodes,hits
                if nodes>=2000 or hits>=55:return
                nodes+=1
                if len(seq)==target:
                    hits+=1
                    new=F|set(seq);add=frozenset(new-orig);drop=frozenset(orig-new);key=(add,drop)
                    if key not in seen:
                        seen.add(key);bank.append((cost,rev,cut,add,drop,frozenset(bads),tuple(seq)))
                    return
                for d in order:
                    v=x^(1<<d)
                    if not(allowed>>v&1) or fmask>>v&1:continue
                    contacts=ne[v] - ({tip} if not seq else set())
                    newcost=cost+len(contacts)
                    if newcost>2:continue
                    seq.append(v);walk(v,fmask|B[x]|1<<x,newcost,bads|contacts);seq.pop()
                    if nodes>=2000 or hits>=55:break
            walk(tip,0,0,set())
    return bank
def main():
    typ,fn,lo,hi,budget=sys.argv[1:];lo,hi,budget=map(int,(lo,hi,budget));ss,fs=load(typ)
    rows=[json.loads(s) for s in (D/(fn+'.jsonl')).read_text().splitlines()];rows=[q for q in rows if q['path']]
    for q in rows[lo:hi]:
        src=q['src'];raw,ch=ss[src];R=q['path'];base=set(raw);rr=set(R)
        family=tails(R,248155+src);rng=random.Random(921856+src)
        family.sort(key=lambda z:(z[0],-len(z[3]),rng.random()))
        if not family:continue
        if family[0][0]==0:
            cost,side,cut,add,rm,contacts,seq=family[0];p=(R[::-1] if side else R)[:len(R)-cut]+list(seq)
            print(json.dumps(dict(status='FOUND',src=src,mode='direct',path=p)),flush=True);return
        oldfam=fs[src];alladd=set().union(*(q[2] for q in oldfam));allrm=set().union(*(q[3] for q in oldfam))
        for mode in (0,1,2):
            if mode==0: sel=family[:10];origlen=4
            elif mode==1:
                sel=[*family[:8],*rng.sample(family,min(18,len(family)))];origlen=16
            else: sel=family;origlen=1000
            blockers=set().union(*(z[5] for z in sel));before=base|alladd
            O=sorted(range(len(oldfam)),key=lambda h:(-len(oldfam[h][3]&blockers),oldfam[h][0]+rng.random()))[:origlen]
            # Distinct time coordinates are unconstrained. Candidate sets have their original physical coordinates.
            add=set().union(*(z[3] for z in sel));drop=set().union(*(z[4] for z in sel));changes=set().union(*(oldfam[h][2]|oldfam[h][3] for h in O))
            pool=rr|base|add|set().union(*(oldfam[h][2] for h in O))
            fixed=rr-drop-changes
            radius=3+mode*2
            for j,v in enumerate(R):
                if v in blockers:fixed-=set(R[max(0,j-radius):j+radius+1])
            for col in [0,1]:
                data=solve(pool,fixed,R,193,budget,col)
                data.update(src=src,mode=mode,majority=col,hard=len(fixed),union=len(pool),grown=len(family),added_beyond_first_union=len(add-before),blockers=len(blockers),min_chords=family[0][0])
                print(json.dumps(data,separators=(',',':')),flush=True)
                if data['path']:return
if __name__=='__main__':main()
