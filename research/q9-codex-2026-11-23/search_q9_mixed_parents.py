"""Force a short private arc from each parent and allow edits throughout Q9."""
import argparse,json
from search_q9_anchored_sets import search
from search_q9_record_unions import alignments,NB
from search_q9_two_flexible_ends import verify

def private_arc(path,i,other):
    return sum(x not in other for x in path[i-2:i+3])>=2
def anchors(p,q,rng):
    ps=set(p);qs=set(q)
    merged=ps&qs
    choices=[[i for i in range(2,len(a)-2) if a[i] not in b and private_arc(a,i,b)] for a,b in ((p,qs),(q,ps))]
    if not all(choices):return
    for _ in range(4):
        i,j=[rng.choice(c) for c in choices]
        a=p[i-2:i+3];b=q[j-2:j+3]
        if any(x==y or y in NB[x] for x in a for y in b):continue
        required=set(a+b)
        # Leave a mutable band around each selected arc, and random holes elsewhere.
        pool=sorted(merged-required)
        rng.shuffle(pool)
        goal=rng.randrange(85,130)
        for v in pool:
            if (v in NB[a[0]] or v in NB[a[-1]] or v in NB[b[0]] or v in NB[b[-1]]) and rng.random()<.8:continue
            if sum(x in required for x in NB[v])>2:continue
            if any(x in required and sum(z in required for z in NB[x])==2 for x in NB[v]):continue
            required.add(v)
            if len(required)>=goal:break
        yield required

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--cases',type=int,default=4000);ap.add_argument('--cap',type=int,default=4000)
    ap.add_argument('--target',type=int,default=192);a=ap.parse_args()
    seen=set()
    for domain,p,q,rng in alignments('/tmp/q9_project_records_input9',300000,582):
        for forced in anchors(p,q,rng):
            key=sum(1<<x for x in forced)
            if key in seen:continue
            seen.add(key)
            st,w=search(forced,set(p),a.target,a.cap)
            if w:verify(w,a.target)
            print(json.dumps([st,hex(key),w],separators=(",",":")),flush=True)
            if w or len(seen)>=a.cases:raise SystemExit
