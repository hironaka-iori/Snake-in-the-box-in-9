from mobile import *
def main():
    rng=random.Random(158071)
    archive=(R/'q9_far189_spring_20261121/comparison191.words').read_text().split()
    excluded={word(path(w)) for w in archive}
    parents=[path(w) for w in archive]
    masks=[m for m in range(512) if m.bit_count()>=3]
    for i in range(int(sys.argv[1])):
        p=rng.choice(parents);m=rng.choice(masks);rep=lambda u:min(u,u^m)
        c=set(map(rep,p))
        # Release neighbourhoods of spatially close, nonconsecutive path segments.
        u=rng.choice(p);near=[x for x in p if (x^u).bit_count()<=3];a=rng.choice(near)
        area={rep(y) for x in (u,a) for b in NB[x] for y in (*NB[b],b)}
        free=c&area;extra=area-c
        s,k,q=solve(p,m,191,256,12000,extra,free,7,excluded)
        print(json.dumps(dict(i=i,mask=m,status=s,vertices=q)),flush=True)
        if q:
            excluded.add(word(q));parents.extend([q]*4)
            for origin in [q,q[::-1]]:
                tip=origin[-1]
                for x in NB[tip]:
                    cand=origin+[x]
                    if valid(cand):
                        print(json.dumps(dict(i=i,status='EXTENDED',vertices=cand)),flush=True);return
            for targetmask in rng.sample(masks,12):
                rep2=lambda x:min(x,x^targetmask); cols=set(map(rep2,q))
                fringe={rep2(t) for e in (q[0],q[-1],u) for v in NB[e] for t in (*NB[v],v)}
                ss,kk,w=solve(q,targetmask,192,256,20000,fringe-cols,fringe&cols,9)
                if w:
                    print(json.dumps(dict(i=i,status='EXTENDED',vertices=w)),flush=True);return
if __name__=='__main__':main()
