"""For each even four-crossing layout find a path or an integer bound for its free upper layer."""
import json,random,sys,subprocess
from pathlib import Path
from itertools import combinations
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
from q9_rigid_ports_tree import export
from q9_rigid_facet_ports import word_path
D=Path("q9_catalogue_four_cross")
def main():
    cases=[r for l in (D/"cases.jsonl").read_text().splitlines() if not (r:=json.loads(l))["parity"]]
    assert len(cases)==260
    rng=random.Random(403215);axes=list(combinations(range(8),3));rng.shuffle(axes)
    scores={}
    for line in (D/"beam.log").read_text().splitlines():
        f=list(map(int,line.split()))
        if len(f)==f[3]+5:scores[f[0]]=f[3]
    cases.sort(key=lambda r:-scores.get(r["case"],-1))
    out=D/"certs";out.mkdir(exist_ok=True)
    for r in cases:
        j=r["case"];tag=out/("c"+str(j));a=word_path(r["word"]);u,v=r["ends"]
        m=u.bit_count()%2;low=set(a)|{u,v};ports={u,v,a[0],a[-1]}
        delta=sum(1-2*(z.bit_count()%2) for z in low)-(1-2*m)
        saved=tag.with_suffix(".json")
        if saved.exists():rec=json.loads(saved.read_text())
        else:
            ans=build(a,ports,low,[0,0],delta,axes[:8])
            if ans is None:
                print(json.dumps(dict(case=j,empty=True)),flush=True);continue
            base,scale,tables,c=ans
            val=base+sum(t[0][2] for _,t in tables)
            assert val==integer_bound(c,low,ports,[0,0],delta)
            rec=dict(word=r["word"],lower_vertices=sorted(low),ports=sorted(ports),upper_endpoint_counts=[0,0],upper_delta=delta,majority=m,total_scaled=val+scale*len(low),cert=c)
            saved.write_text(json.dumps(rec,separators=(",",":")))
        cap=rec["total_scaled"]/rec["cert"]["scale"]
        report=dict(case=j,integer_root=rec["total_scaled"],scale=rec["cert"]["scale"])
        if cap>=193:
            export(rec,tag.with_suffix(".tables"))
            result=subprocess.check_output(["q9_facet_priced_tree_20261121/tree",str(tag),str(tag.with_suffix(".tree")),"193","60000"],text=True)
            verify=subprocess.check_output(["q9_facet_priced_tree_20261121/replay",str(tag.with_suffix(".tables")),str(tag.with_suffix(".tree")),"193"],text=True)
            report.update(tree=result.strip(),replay=verify.strip())
        print(json.dumps(report),flush=True)
        if "tree" in report and " found 0 " not in report["tree"]:return
if __name__=="__main__":main()
