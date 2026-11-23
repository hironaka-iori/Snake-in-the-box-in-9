"""Search the longest source fragments that can coexist with an independent three-vertex bend."""
import json,random,subprocess,sys
from pathlib import Path
from itertools import combinations
from q9_classify_record_donor_windows import canonical
from q9_rigid_facet_ports import word_path
from q9_rigid_ports_tree import export
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
D=Path("q9_lower_bend");N=[{x^1<<d for d in range(8)} for x in range(256)]
def cases():
    words=Path("q8_catalogue_96_98.words").read_text().split()+Path("q8_single_cross_complete_arms.txt").read_text().split()
    for size in (95,94,93):
        bank=sorted({canonical(w[j:j+size]) for w in words for j in range(len(w)-size+1)})
        for w in bank:
            low=set(word_path(w));free={v for v in range(256) if v not in low and not N[v]&low}
            for c in sorted(free):
                for u,v in combinations(sorted(N[c]&free),2):yield w,(u,c,v)
def main():
    D.mkdir(exist_ok=True);out=D/"prices";out.mkdir(exist_ok=True)
    ax=list(combinations(range(8),3));random.Random(403215).shuffle(ax)
    for j,(w,bend) in enumerate(cases()):
        p=word_path(w);low=set(p)|set(bend);ports={p[0],p[-1],bend[0],bend[-1]}
        for ends in ([2,0],[0,2],[1,1]):
            m=0 if ends[0]==2 else 1 if ends[1]==2 else -1
            delta=sum(1-2*(v.bit_count()%2) for v in low)-(ends[0]-ends[1])//2
            tag=out/f"b{j}_m{m}";store=tag.with_suffix(".json")
            if store.exists():r=json.loads(store.read_text())
            else:
                a=build(p,ports,low,ends,delta,ax[:8])
                if a is None:
                    print(json.dumps(dict(case=j,bend=bend,word=w,ends=ends,empty=True)),flush=True);continue
                base,scale,tables,c=a
                value=base+sum(t[0][2] for _,t in tables);assert integer_bound(c,low,ports,ends,delta)==value
                r=dict(word=w,lower_vertices=sorted(low),ports=sorted(ports),upper_endpoint_counts=ends,upper_delta=delta,majority=m,total_scaled=value+len(low)*scale,cert=c)
                store.write_text(json.dumps(r,separators=(",",":")))
            res=dict(case=j,bend=bend,word=w,ends=ends,root=r["total_scaled"],scale=r["cert"]["scale"])
            if m!=-1 and r["total_scaled"]>=193*r["cert"]["scale"]:
                export(r,tag.with_suffix(".tables"))
                res["tree"]=subprocess.check_output(["q9_facet_priced_tree_20261121/tree",str(tag),str(tag.with_suffix(".tree")),"193","220000"],text=True).strip()
                res["checked"]=subprocess.check_output(["q9_facet_priced_tree_20261121/replay",str(tag.with_suffix(".tables")),str(tag.with_suffix(".tree")),"193"],text=True).strip()
            print(json.dumps(res),flush=True)
            if "tree" in res and " found 0 " not in res["tree"]:return
if __name__=="__main__":main()
