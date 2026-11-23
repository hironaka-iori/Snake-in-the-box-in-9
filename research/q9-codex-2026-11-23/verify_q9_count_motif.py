"""Replay the motif with direct vertex bitsets, without the graph implementation."""
import argparse
import json
from pathlib import Path

from q9_window_geometry import canonical


def positions(word):
    result=[0]
    for i in word:
        result.append(result[-1]^(1<<i))
    return result


def check(data,horizon):
    dimension=data["dimension"]
    masks=[sum(1<<(v^(1<<i)) for i in range(dimension))|(1<<v)
           for v in range(1<<dimension)]
    states={tuple(word) for word in data["initial"]}
    sizes=[len(states)]
    for row in data["layers"]:
        allowed=set(map(tuple,row))
        next_states=set()
        for tail in states:
            points=positions(tail)
            blocked=0
            for point in points[:-1]:
                blocked |= masks[point]
            for i in range(dimension):
                if blocked>>(points[-1]^(1<<i))&1:
                    continue
                extension=tail+(i,)
                if canonical(extension[-9:]) in allowed:
                    next_states.add(canonical(extension[-(horizon-1):]))
        states=next_states
        sizes.append(len(states))
        if not states:
            break
    return dict(width=horizon,state_counts=sizes,exhausted=not states)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("data",type=Path)
    p.add_argument("width",nargs="+",type=int)
    a=p.parse_args()
    data=json.loads(a.data.read_text())
    for w in a.width:
        print(json.dumps(check(data,w)),flush=True)
