"""Price opposite-colour four-crossing cases. All global endpoints are fixed in the lower Q8."""
import json,random
from pathlib import Path
from itertools import combinations
from q9_rigid_facet_ports import word_path
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
D=Path("q9_catalogue_four_cross")
def main():
    args=__import__("sys").argv;piece=int(args[1]);pieces=int(args[2])
    out=D/"odd_certs";out.mkdir(exist_ok=True)
    axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
    for l in (D/"cases.jsonl").read_text().splitlines():
        r=json.loads(l);j=r["case"]
        if not r["parity"] or j%pieces!=piece:continue
        a=word_path(r["word"]);u,v=r["ends"];low=set(a)|{u,v};ports={a[0],a[-1],u,v}
        assert (u^v).bit_count()%2==1
        delta=sum(1-2*(x.bit_count()%2) for x in low)
        path=out/f"c{j}.json"
        if path.exists():result=json.loads(path.read_text())
        else:
            for directions in (4,8,14):
                arg=build(a,ports,low,[0,0],delta,axes[:directions])
                if arg is None:
                    result=dict(case=j,empty_table=True,axes=axes[:directions]);break
                base,scale,tables,c=arg
                root=base+sum(t[0][2] for _,t in tables)
                assert integer_bound(c,low,ports,[0,0],delta)==root
                result=dict(case=j,total_scaled=root+scale*len(low),cert=c)
                if result["total_scaled"]<194*scale:break
            temp=path.with_suffix(".tmp");temp.write_text(json.dumps(result,separators=(",",":")));temp.replace(path)
        print(json.dumps({k:v for k,v in result.items() if k!="cert"}),flush=True)
if __name__=="__main__":main()
