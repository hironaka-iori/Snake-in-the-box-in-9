from repair import *
pp=placements()
for rank in map(int,sys.argv[1:]):
    r=rows[rank];old=set(r['oldfixed']);s=set(old);rng=random.Random(7341+rank)
    order=sorted(old-{r['ep']});rng.shuffle(order);guide=pp[rank,0][0];log=[]
    # Discharge assumptions one block at a time without carrying their dependent domain reductions.
    for start in range(0,len(order),13):
        probe=set(order[start:start+13])&s
        z=solve(r,s-probe,guide,18000,r['majority'],sorted(probe))
        if z['result']=='UNSAT':s=(s-probe)|set(z['core'])
        log.append(dict(probe=sorted(probe),status=z['result'],core=z.get('core'),kept=len(s),conflicts=z['conflicts']))
    print(json.dumps(dict(rank=rank,freed=sorted(old-s),mandatory=sorted(s),history=log)),flush=True)
