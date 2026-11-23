"""Mix a near-path with cube isometries that fix separated pairs of its vertices."""
from argparse import ArgumentParser
import json
from random import Random
from pathlib import Path
from search_q9_time_vertex_lists import solve_domains
from search_q9_parent_junctions import check

def domains(p,rng,moves):
    """Each additional old-to-new mapping supplies a complete interior alternative."""
    D=[{v} for v in p]
    for _ in range(moves):
        start,end=sorted(rng.sample(range(len(p)),2))
        if end-start<4:continue
        delta=p[start]^p[end]
        perm=list(range(9))
        # A cube isometry fixing both ends may permute the differing and equal bits separately.
        for bit in (0,1):
            cells=[i for i in range(9) if (delta>>i)&1==bit]
            reorder=cells[:]
            rng.shuffle(reorder)
            for a,b in zip(cells,reorder):perm[a]=b
        if rng.randrange(2)==0:
            cells=[(a,b) for a in range(9) for b in range(a) if ((delta>>a)^(delta>>b))&1==0]
            a,b=rng.choice(cells)
            perm=list(range(9))
            perm[a],perm[b]=b,a
        reverse=rng.randrange(3)==0
        anchor=p[end] if reverse else p[start]
        for j in range(start+1,end):
            old=p[start+end-j] if reverse else p[j]
            image=p[start]^sum(1<<b for a,b in enumerate(perm) if (old^anchor)&(1<<a))
            D[j].add(image)
    for end,near in ((0,1),(-1,-2)):
        D[end].update(v^(1<<d) for v in D[near] for d in range(9))
    return D

def main():
    ap=ArgumentParser()
    ap.add_argument("src",type=Path)
    ap.add_argument("--count",type=int,default=100)
    ap.add_argument("--moves",type=int,default=75)
    ap.add_argument("--seed",type=int,default=4792)
    ap.add_argument("--budget",type=int,default=1500)
    ap.add_argument("--control",action="store_true")
    args=ap.parse_args()
    bank=[list(map(int,s.split())) for s in args.src.read_text().splitlines()]
    rng=Random(args.seed)
    for job in range(args.count):
        i=rng.randrange(len(bank))
        p=bank[i]
        if args.control:
            p=json.loads(Path("q9_segment_tips_control191.json").read_text())["vertices"]
        opts=domains(p,rng,args.moves)
        seed=p.copy()
        if args.control:
            # Scramble the solver's preference in the interior; the original valid assignment stays available.
            seed=[rng.choice(sorted(o)) for o in opts]
        status,w=solve_domains(seed,opts,args.budget)
        if w:check(w,len(p)-1)
        print(json.dumps(dict(job=job,source=i,options=sum(map(len,opts)),status=status,witness=w)),flush=True)
        if w and len(w)>=193:return
if __name__=="__main__":main()
