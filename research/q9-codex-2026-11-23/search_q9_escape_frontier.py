"""Recombine each successfully escaped witness with its own defective starting path."""
import json
from pathlib import Path
from search_q9_break_matched_anchors import cases,check,search

def main():
    originals={(n,r):set(p) for n,r,p,_,_,_ in cases()}
    universe=set(range(512))
    seen=set()
    for control in map(json.loads,Path("q9_break_matched_191.jsonl").read_text().splitlines()):
        witness=control["witness"]
        if witness is None:continue
        check(witness,191)
        old=originals[control["source"],control["row"]]
        new=set(witness)
        shared=old & new
        for fresh in sorted(new-old):
            for dropped in sorted((old-new)-{control["omitted"]}):
                for radius in [1,2,3]:
                    # Require material from each parent while freeing a pair of neighborhoods.
                    fixed={v for v in shared if min((v^fresh).bit_count(),(v^dropped).bit_count())>radius}
                    fixed.update([fresh,dropped])
                    forbidden=control["omitted"]
                    k=(frozenset(fixed),forbidden)
                    if k in seen:continue
                    seen.add(k)
                    status,p=search(fixed,new,192,5000,allowed=universe-{forbidden},at_least=True)
                    if p:
                        check(p,192)
                        assert fixed<=set(p) and forbidden not in p
                    print(json.dumps(dict(source=control["source"],row=control["row"],omitted=forbidden,
                        fresh=fresh,dropped=dropped,radius=radius,fixed=len(fixed),status=status,witness=p)),flush=True)
                    if p:return
if __name__=="__main__":main()
