"""Increase the minority side of 189-edge seeds by one orbit and seek 192 edges."""
import itertools
import json
import random
from q9_pair_selector import search
from verify_q9_center_avoidance import verify


def main():
    rows=json.load(open("q9_center_avoidance_verified.json"))["new_witnesses"]
    for index,row in enumerate(rows):
        p=row["vertices"]
        verify(p)
        assert len(p)==190
        for parity in (0,1):
            side=set(p[parity::2])
            rng=random.Random(811249+index*13+parity)
            masks=[t for t in range(1,512) if t.bit_count() in (2,4)]
            for t in rng.sample(masks,16):
                pairs=sorted((v,v^t) for v in side if (v^t) not in side)
                if len(pairs)==len(side):continue
                # Control seeks 190 edges with the original 95 minority vertices
                # allowed to switch within their respective pairs as well.
                st,w=search(side,pairs,t,set(p),190,3500)
                print(json.dumps([index,parity,t,None,190,st,w],separators=(",",":")),flush=True)
                empty=[v for v in range(512) if not (v^p[parity]).bit_count()%2 and
                    v<(v^t) and v not in side and (v^t) not in side]
                for v in rng.sample(empty,min(6,len(empty))):
                    st,w=search(side|{v},pairs+[(v,v^t)],t,set(p),192,3500)
                    print(json.dumps([index,parity,t,v,192,st,w],separators=(",",":")),flush=True)
                    if w:return


if __name__=="__main__":main()
