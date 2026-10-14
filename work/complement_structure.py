import json
from pathlib import Path
seed=json.loads(Path('outputs/snake8_witness.json').read_text())['vertex_sequence']
for root in [seed[0],seed[-1]]:
    allowed=set(range(256)) - {v ^ root for v in seed} | {0}
    components=[]
    unseen=set(allowed)
    while unseen:
        front=[unseen.pop()]
        component=set(front)
        while front:
            v=front.pop()
            for k in range(8):
                w=v^(1<<k)
                if w in unseen:
                    unseen.remove(w);component.add(w);front.append(w)
        components.append(component)
    rootcomponent=next(c for c in components if 0 in c)
    degrees={v:sum((v^(1<<k)) in rootcomponent for k in range(8)) for v in rootcomponent}
    hist={d:list(degrees.values()).count(d) for d in sorted(set(degrees.values()))}
    print(root, 'components',sorted(map(len,components)), 'degree histogram',hist,'parity',[sum(v.bit_count()%2==p for v in rootcomponent) for p in [0,1]])
