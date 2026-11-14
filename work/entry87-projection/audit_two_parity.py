"""Compare incremental degrees and connectivity with an independent explicit graph."""
from itertools import combinations
from pathlib import Path
from random import Random
import subprocess
from solve import paths


def literal(anchors,p):
    adj={v:set() for v in anchors};tips=set()
    for w in range(512):
        if w.bit_count()%2==p:continue
        nbr=[v for v in anchors if (v^w).bit_count()==1]
        if len(nbr)==1:
            tips.add(nbr[0])
        if len(nbr)==2:
            a,b=nbr;adj[a].add(b);adj[b].add(a)
    unseen=set(anchors);stack=[unseen.pop()]
    while stack:
        new=adj[stack.pop()]&unseen
        unseen-=new;stack.extend(new)
    leaves={v for v in anchors if len(adj[v])==1}
    return len(anchors),sum(not adj[v] for v in anchors),len(leaves),len(leaves-tips),int(not unseen)


def audit(checker,rounds=800):
    rng=Random(317042)
    for p in (0,1):
        initial=set(paths()[1][p::2])
        all_words={v for v in range(512) if v.bit_count()%2==p}
        sequence=[];state=set(initial)
        for _ in range(rounds):
            # Alternating insertions and deletions explore unrelated anchor sets.
            word=rng.choice(sorted(state if len(state)>=len(initial) else all_words-state))
            state.symmetric_difference_update({word});sequence.append(word)
        data=" ".join(map(str,[len(initial),*sorted(initial),*sequence]))
        proc=subprocess.run([str(checker),"--inspect",str(p)],input=data,text=True,
                            capture_output=True,check=True)
        lines=proc.stdout.splitlines();assert len(lines)==len(sequence)
        state=set(initial)
        for word,line in zip(sequence,lines):
            state.symmetric_difference_update({word})
            assert tuple(map(int,line.split()))==literal(state,p)
        print("checked",p,len(lines),flush=True)


if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument("--exe",type=Path,default=Path("two-parity.exe"))
    args=parser.parse_args()
    audit(args.exe.resolve())
