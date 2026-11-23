"""Independently enumerate endpoint-rooted isometries with integer bitsets."""
import itertools
import json
from collections import Counter
from pathlib import Path
from verify_q9_center_avoidance import verify,forms
def rooted(p,r):
    q=p[::-1] if r else p
    return [v^q[0] for v in q]
def get_pool():
    out={}
    for name in ("q8_joint_even_arms.txt","q8_exchange_new_rooted_arms.txt","q8_exchange_second_rooted_arms.txt","q8_two_crossing_middle_seeds.txt"):
        for seq in Path(name).read_text().split():
            if len(seq)<97:continue
            p=[0]
            for c in seq:p.append(p[-1]^(1<<int(c)))
            k=forms(p,len(seq))[0];out.setdefault(k,p)
    return [p for k,p in sorted(out.items(),key=lambda kv:(-len(kv[0]),kv[0]))]
def go():
    donors=[r["vertices"] for r in json.load(open("q8_bitterman_97.json"))["rows"]]
    pool=get_pool()+donors
    for p in pool:verify(p);assert max(p)<256
    assert len(donors)==18 and len(pool)==26
    obs={(j,s,i,r):h for h,i,r,j,s,p,q in map(json.loads,open("q8_bitterman_min_overlaps.jsonl"))}
    left=[(i,r,sum(1<<v for v in rooted(p,r))) for i,p in enumerate(donors) for r in (0,1)]
    # Relabel each transition in the right arm forward, unlike the first calculation.
    moves={}
    for j,b in enumerate(pool):
        for s in (0,1):
            q=rooted(b,s)
            moves[j,s]=[(a^v).bit_length()-1 for a,v in zip(q,q[1:])]
    best={key:999 for key in obs}
    for perm in itertools.permutations(1<<d for d in range(8)):
        for (j,s),word in moves.items():
            acc=1;v=0
            for d in word:v^=perm[d];acc|=1<<v
            for i,r,mask in left:
                key=j,s,i,r;h=(acc&mask).bit_count()
                if h<best[key]:best[key]=h
    assert best==obs
    init={tuple(r[:3]):r[3] for r in map(json.loads,open("q9_bitterman_free_192.jsonl"))}
    for r in map(json.loads,open("q9_bitterman_free_deep.jsonl")):
        k=tuple(r[:3]);assert init[k]=="UNKNOWN";init[k]=r[3]
    dkeys={forms(p,97)[0].hex() for p in donors}
    assert len(dkeys)==18 and set(init)=={(k,e,g) for k in dkeys for e,g in [(0,192),(1,192),(0,193)]}
    assert set(init.values())<=set(("EXHAUSTED","DUAL_EXCLUSION"))
    rep=list(map(json.loads,open("q9_bitterman_layer_repair.jsonl")));verify(rep[0][-1]);assert len(rep[0][-1])==192 and rep[0][-2]=="FOUND"
    return dict(donors=len(donors),rooted_pairs=len(best),placements=len(best)*40320,minimum_projected_overlap=min(best.values()),minimum_extra_vertical_contacts=min(best.values())-1,free_other_vertices_cases=dict(Counter(init.values())),local_repairs={str(k):n for k,n in Counter((z[6]+z[7]+1,z[-2]) for z in rep[1:]).items()})
if __name__=="__main__":print(json.dumps(go(),indent=2))
