"""Search three-crossing extensions: both ends of the lower donor cross and one isolated lower vertex is a global endpoint."""
from itertools import combinations
from pathlib import Path
import json,random,subprocess,sys
from q9_rigid_facet_ports import word_path
from q9_rigid_ports_tree import export
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
D=Path("q9_catalogue_three_cross")
def main():
    D.mkdir(exist_ok=True);out=D/"cases";out.mkdir(exist_ok=True)
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    score={}
    for f in ["q9_facet_bank_four.jsonl","q9_facet_bank_all8.jsonl"]:
        for ln in Path(f).read_text().splitlines():
            if not ln.endswith("}"):continue
            r=json.loads(ln);key=(r["index"],r["majority"]);score[key]=min(score.get(key,512),r["bound_scaled"]/r["scale"])
    jobs=[]
    for i,w in enumerate(bank):
        a=word_path(w);F=set(a)
        for x in range(256):
            if x not in F and not any(x^(1<<d) in F for d in range(8)):
                jobs.append((score.get((i,x.bit_count()%2),202),i,x))
    assert len(jobs)==1496
    random.Random(2304).shuffle(jobs);jobs.sort(key=lambda z:-z[0])
    ax=list(combinations(range(8),3));random.Random(403215).shuffle(ax)
    for seedscore,i,x in jobs:
        tag=out/f"d{i}_x{x}";w=bank[i];a=word_path(w);m=x.bit_count()%2
        low=set(a)|{x};ports={a[0],a[-1],x};ends=[int(c==m) for c in (0,1)]
        delta=sum(1-2*(v.bit_count()%2) for v in low)-(1-2*m)
        recfile=tag.with_suffix(".json")
        if recfile.exists():r=json.loads(recfile.read_text())
        else:
            ans=build(a,ports,low,ends,delta,ax[:8])
            if ans is None:
                print(json.dumps(dict(i=i,x=x,empty=True)),flush=True);continue
            base,s,ts,c=ans;val=base+sum(t[0][2] for _,t in ts);assert val==integer_bound(c,low,ports,ends,delta)
            r=dict(word=w,lower_vertices=sorted(low),ports=sorted(ports),majority=m,upper_endpoint_counts=ends,upper_delta=delta,total_scaled=val+s*len(low),cert=c)
            recfile.write_text(json.dumps(r,separators=(",",":")))
        result=dict(i=i,x=x,root=r["total_scaled"],scale=r["cert"]["scale"])
        if r["total_scaled"]>=193*r["cert"]["scale"]:
            export(r,tag.with_suffix(".tables"))
            rr=subprocess.check_output(["q9_facet_priced_tree_20261121/tree",str(tag),str(tag.with_suffix(".tree")),"193","120000"],text=True)
            result["tree"]=rr.strip()
            result["verify"]=subprocess.check_output(["q9_facet_priced_tree_20261121/replay",str(tag.with_suffix(".tables")),str(tag.with_suffix(".tree")),"193"],text=True).strip()
        print(json.dumps(result),flush=True)
        if "tree" in result and " found 0 " not in result["tree"]:return
if __name__=="__main__":main()
