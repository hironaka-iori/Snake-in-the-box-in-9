"""Generate mixed-parent snakes explicitly avoiding all excluded 142-edge center shapes."""
import json,random,argparse
from q9_avoiding_centers import reference,code
from search_q9_anchored_sets import search
from search_q9_two_flexible_ends import verify

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--start",type=int,default=0)
    ap.add_argument("--stop",type=int,default=1000)
    args=ap.parse_args()
    k=142;bank=reference(k);rng=random.Random(142192)
    rows=list(map(json.loads,open("q9_mixed_parents_192.jsonl")))
    rng.shuffle(rows)
    def forbidden(p):
        changes=[a^b for a,b in zip(p,p[1:])]
        for i in range(len(p)-k):
            if code(changes[i:i+k]) in bank:
                return p[i:i+k+1]
        return None
    # A blocked center returns exactly its 143 vertices, also for reversed paths.
    ref=list(map(int,open('/tmp/q9_domain_all190_centers20.txt').readline().split()))
    assert len(forbidden(ref))==len(forbidden(ref[::-1]))==143
    for _,key,_ in rows[args.start:args.stop]:
        mask=int(key,16);fixed={v for v in range(512) if mask>>v&1}
        for target in (192,190,189):
            st,w=search(fixed,fixed,target,3200,reject_fragment=forbidden)
            if w:
                verify(w,target)
                assert not forbidden(w)
            print(json.dumps([st,key,target,w],separators=(',',':')),flush=True)
            if w and target==192:return
            if w:break
if __name__=='__main__':main()
