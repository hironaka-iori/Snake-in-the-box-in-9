"""Recheck witnesses, expected cases, and monotone implications between window sizes."""
from collections import Counter
import gzip
import json
from pathlib import Path
from match_q9_onechord_obstruction import canonical,images_in_graph,longest_component

def rows(name):
    return [json.loads(s) for s in Path(name+".jsonl").read_text().splitlines()]

def key(row):
    return row["source"],row["row"],row["omitted"]

def main():
    report=json.loads(Path("q9_onechord_62anchors.json").read_text())
    a=set(report["anchors"])
    expected={(x["input"],x["row"],v) for x in report["results"] for v in x["images"][0]}
    banks={name:[list(map(int,s.split())) for s in Path(name).read_text().splitlines()] for name in {n for n,_,_ in expected}}
    exclusions={}
    for f in ["width6","width6_deep","width12","midrange","midrange_deep","radius9_retry"]:
        for r in rows("q9_break_matched_"+f):
            k=key(r)
            assert k in expected and r["target"]==192 and r["witness"] is None
            if r["status"]=="UNSAT":
                exclusions[k]=max(exclusions.get(k,0),r["width"])
            else:assert r["status"]=="UNKNOWN"
    assert len(expected)==2232 and exclusions.keys()==expected
    with gzip.open("q9_port_followup_public191.txt.gz","rt") as infile:
        known={canonical(list(map(int,line.split()))) for line in infile}
    valid=0
    classes=set()
    free_classes=set()
    chain=longest_component(a)
    for r in rows("q9_break_matched_191"):
        if r["witness"] is None:continue
        p=r["witness"]
        assert len(p)==len(set(p))==192 and all(0<=v<512 for v in p) and r["omitted"] not in p
        assert all(((p[i]^p[j]).bit_count()==1)==(j==i+1) for j in range(len(p)) for i in range(j))
        source=banks[r["source"]][r["row"]]
        chords=[(i,j) for j in range(len(source)) for i in range(j-1) if (source[i]^source[j]).bit_count()==1]
        (a0,b0),=chords
        centers=[0,len(source)-1,a0,b0,source.index(r["omitted"])]
        fixed={v for i,v in enumerate(source) if all(abs(i-k)>r["width"] for k in centers)}
        assert len(fixed)==r["anchors"] and fixed<=set(p)
        shape=canonical(p)
        valid+=1
        classes.add(shape)
        if not images_in_graph(set(p),chain,a):free_classes.add(shape)
    return dict(candidates=report["matched"],cases=len(expected),
                solver_exclusions_by_radius={rad:sum(w>=rad for w in exclusions.values()) for rad in (6,7,8,9,12)},
                validated_191=valid,classes_191=len(classes),new_191=len(classes-known),
                obstruction_free_classes=len(free_classes))
if __name__=="__main__":print(json.dumps(main(),indent=2))
