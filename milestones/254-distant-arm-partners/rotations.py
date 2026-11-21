"""Compare the two endpoint rotations with every member of the 68-edge catalogue."""
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
LAST=HERE.parent/"253-repeated-segment-growth"
sys.path.insert(0,str(LAST))
from thresholds import transitions,windows,diagonal_best


def main():
    latest=HERE/"parity-families.json"; base=LAST/"closure.json"
    new=json.loads(latest.read_bytes()); old=json.loads(base.read_bytes())["paths"]
    sets={k:set(p) for k,p in new["shapes"].items()}
    common=set.intersection(*sets.values())
    pairs=((83,209),(17,177),(132,149))
    patterns={tuple(next(x for x in pair if x in v) for pair in pairs):k for k,v in sets.items()}
    if len(common)!=94 or len(patterns)!=8 or any(sets[k]!=common|set(c) for c,k in patterns.items()):
        raise ValueError("Parent vertex sets do not give the three independent choices")
    out={}
    old_words={k:transitions(p) for k,p in old.items()}
    for k in new["outside_previous"]:
        path=new["shapes"][k];w=transitions(path)
        parents=[a for a in sets.keys()&old.keys() if len(sets[k]&sets[a])==96]
        if not parents: raise ValueError("Missing one-vertex exchange with the previous catalogue")
        lo,hi=0,97;test={}
        while hi-lo>1:
            width=(lo+hi)//2;bucket={code for code,_,_ in windows(w,width)}
            hits=[a for a,b in old_words.items() if any(code in bucket for code,_,_ in windows(b,width))]
            test[width]=hits
            if hits:lo=width
            else:hi=width
        old_id=test[lo][0]
        if lo>=68 or diagonal_best(w,old_words[old_id])!=lo:raise ValueError("Invalid maximum overlap")
        out[k]=dict(maximum_common_edges=lo,attaining_old_ids=sorted(test[lo]),one_vertex_exchanges=sorted(parents))
    result=dict(pins={p.name:sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),latest,base,LAST/"thresholds.py")},
        common_vertices=sorted(common),pairs=pairs,choices=[dict(sites=pat,shape=k) for pat,k in sorted(patterns.items())],
        outside=out)
    (HERE/"rotations.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
    print({k[:8]:r["maximum_common_edges"] for k,r in out.items()})


if __name__=="__main__":main()
