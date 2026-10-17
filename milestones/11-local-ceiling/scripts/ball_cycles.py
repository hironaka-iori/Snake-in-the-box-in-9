"""For each window (k centres) of an adversary union of cycles, does the radius-r ball around
the centres contain a complete cycle?  If never, every ball sees only path pieces."""
import json, sys
d=json.load(open(sys.argv[1])); cycles=d['cycles']
def dist(a,b): return bin(a^b).count('1')
for r in (3,4,5):
    for k in (3,4,5,6):
        worst=0; hit=0; tot=0
        for c in cycles:
            L=len(c)
            for st in range(L):
                cen=[c[(st+i)%L] for i in range(1,k+1)]
                tot+=1
                full=any(all(min(dist(v,x) for x in cen)<=r for v in cyc) for cyc in cycles)
                hit+=full
        print(f"r={r} k={k}: windows with a complete cycle inside the ball: {hit}/{tot}", flush=True)
