"""Seek a 191-edge class outside the frozen archive among rigid donors ruled out for 192."""
from pathlib import Path
from itertools import combinations
import json,subprocess,random
from q9_rigid_facet_ports import word_path
from q9_rigid_ports_tree import export
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
from q9_classify_record_donor_windows import canonical
D=Path("q9_rigid_odd191")
def tree(tag,limit,inp=None):
    tr=tag.with_suffix(".tree")
    c=[str(D/"tree"),str(tag),str(tr),"192",str(limit)]
    v=[str(D/"replay"),str(tag.with_suffix(".tables")),str(tr),"192"]
    if inp:c.append(str(inp));v.append(str(inp))
    log=subprocess.check_output(c,text=True).strip()
    ck=subprocess.check_output(v,text=True).strip()
    return log,ck
def run():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    summary=json.loads(Path("q9_all_rigid_audit.json").read_text())
    assert summary["closed"]==41
    known={canonical(w) for w in Path("q9_far189_spring_20261121/comparison191.words").read_text().split()}
    cases=[(int(k),r["stats"]["nodes"]) for k,r in summary["records"].items() if "stats" in r]
    old=json.loads(Path("q9_rigid_five_witnesses.json").read_text())["43"]["vertices"]
    axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
    order=[(43,0)]+sorted(cases,key=lambda x:-x[1])
    for i,_ in order:
        w=bank[i];arm=word_path(w);low=set(arm);tips={arm[0],arm[-1]}
        for ports in [(arm[0],arm[-1]),(arm[0],),(arm[-1],)]:
            if i==43 and set(ports)!={x for x in low if x+256 in old}:continue
            tag=D/("d%d_p%s"%(i,"-".join(map(str,ports))))
            ends=[1-len(tips-set(ports)),1]
            delta=sum(1-2*(v.bit_count()%2) for v in low)
            result=build(arm,ports,low,ends,delta,axes[:12])
            if result is None:continue
            base,scale,ts,c=result;val=base+sum(t[0][2] for _,t in ts)
            assert val==integer_bound(c,low,set(ports),ends,delta)
            r=dict(word=w,ports=ports,majority=-1,upper_endpoint_counts=ends,upper_delta=delta,total_scaled=val+scale*len(low),cert=c)
            tag.with_suffix(".json").write_text(json.dumps(r,separators=(",",":")))
            report=dict(index=i,ports=ports,root=r["total_scaled"],scale=scale)
            if r["total_scaled"]>=192*scale:
                export(r,tag.with_suffix(".tables"));pins=None
                if i==43:
                    pins=tag.with_suffix(".pins");pool=(set(range(256))-low)|set(ports)
                    pins.write_text("".join(f"{x+256} {int(x+256 in old)}\n" for x in sorted(pool)))
                report["tree"],report["checked"]=tree(tag,120000,pins)
                if " found 0 " not in report["tree"]:
                    for ln in tag.with_suffix(".tree").open():
                        if not ln.startswith("H "):continue
                        n,*p=map(int,ln.split()[1:]);assert n==len(p)==len(set(p))==192 and low=={v for v in p if v<256}
                        assert all(0<=v<512 for v in p) and all(((v^u).bit_count()==1)==(j+1==k) for k,v in enumerate(p) for j,u in enumerate(p[:k]))
                        word=canonical("".join(str((u^v).bit_length()-1) for u,v in zip(p,p[1:])))
                        report.update(vertices=p,known=word in known);break
                if i==43:assert report["known"]
            print(json.dumps(report),flush=True)
            if "known" in report and not report["known"]:return
if __name__=="__main__":run()
