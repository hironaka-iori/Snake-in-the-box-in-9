"""Enumerate every one-vertex exchange that preserves a 49-edge path in Q7."""
from argparse import ArgumentParser
from collections import defaultdict,deque
from parents import HERE,read,write,points,unrooted,paircheck

NEAR=[{v^(1<<d) for d in range(7)} for v in range(128)]

def exchanged(p):
    marked=set(p)
    contacts={v:NEAR[v]&marked for v in range(128)}
    out={}
    for i,gone in enumerate(p):
        needed=len(contacts[gone])
        for put in range(128):
            if put in marked:continue
            touch=contacts[put]-{gone}
            if len(touch)!=needed:continue
            if any(len(contacts[v]-{gone})==2 for v in touch):continue
            selected=(marked-{gone})|{put}
            tip=next((v for v in sorted(selected) if len(NEAR[v]&selected)==1),None)
            if tip is None:continue
            order=[tip]
            while len(order)<50:
                options=(NEAR[order[-1]]&selected)-set(order[-2:])
                if len(options)!=1:break
                order.append(next(iter(options)))
            if len(order)!=50:continue
            code=unrooted(order)
            out.setdefault(code,[]).append([i,put])
    return out

def independent(p):
    occupied=set(p)
    out={}
    for i in range(len(p)):
        pieces=[q for q in (p[:i],p[i+1:]) if q]
        a=pieces[0]
        for end in {a[0],a[-1]}:
            for v in NEAR[end]-occupied:
                near=NEAR[v]&(occupied-{p[i]})
                if near&set(a)!={end}:continue
                left=a if a[-1]==end else a[::-1]
                if len(pieces)==2:
                    b=pieces[1];matches=near&set(b)
                    if len(matches)!=1:continue
                    ep=next(iter(matches))
                    if ep not in {b[0],b[-1]}:continue
                    new=left+[v]+(b if b[0]==ep else b[::-1])
                else:new=left+[v]
                code=unrooted(new)
                out.setdefault(code,set()).add((i,v))
    return {k:sorted([list(x) for x in v]) for k,v in out.items()}

def main():
    ap=ArgumentParser();ap.add_argument("source");a=ap.parse_args()
    starts=set(read(HERE/a.source)["parents"])|set(read(HERE/"project-intervals.json")["parents"])
    graph={}; seen=set(starts);work=deque(sorted(starts))
    while work:
        k=work.popleft();p=points(bytes.fromhex(k))
        paircheck(p,7)
        children=exchanged(p)
        assert children==independent(p)
        graph[k]=children
        for c in sorted(children):
            if c not in seen:work.append(c);seen.add(c)
    components=[];remain=set(seen)
    while remain:
        group={min(remain)};q=list(group)
        for k in q:
            for c in graph[k]:
                assert k in graph[c]
                if c not in group:q.append(c);group.add(c)
        components.append(sorted(group));remain-=group
    data=dict(seed_window=a.source,starts=sorted(starts),parents=sorted(seen),components=components,moves=graph)
    write(HERE/"q7-parents.json",data)
    print("Exchange closure",len(starts),len(seen),[len(c) for c in components],flush=True)

if __name__=="__main__":main()
