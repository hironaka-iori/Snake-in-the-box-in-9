"""Check two-replacement survivors and reconstruct every positive cube witness."""
import argparse
from collections import Counter
from math import comb
from pathlib import Path
import subprocess
from parity_edits import force
from parity_skeleton import complete
from solve import paths,save,defects


def check(p,start,end,core,exe):
    base=sorted(paths()[1][p::2]);run=subprocess.run(
        [str(exe),str(p),str(start),str(end),str(int(core))],
        input=" ".join(map(str,base)),text=True,capture_output=True,check=True)
    lines=run.stdout.splitlines()
    tag,tests,degree,conn,skip=lines.pop().split()
    assert tag=="count" and int(conn)==len(lines)
    eligible=[(base[i],base[j]) for i in range(start,end) for j in range(i+1,len(base))]
    selected=[s for s in eligible if not core or set(s)&{0,6,17,18}]
    assert int(skip)==len(eligible)-len(selected)
    assert int(tests)==len(selected)*comb(256-len(base),2)
    fname=Path(f"two-parity-{p}-{start}-{end}-"+("core" if core else "all")+".json")
    stats=Counter();details=[];witnesses=[]
    for line in lines:
        a,b,x,y=map(int,line.split())
        edited=(set(base)-{a,b})|{x,y}
        assert len(edited)==len(base)
        reason,why=force(sorted(edited),bool(p))
        # The native counter checked disconnection, isolated anchors and invalid leaves.
        assert reason not in ("disconnected","endpoint degrees")
        if reason is None:
            result=complete(sorted(edited),bool(p))
            reason=result.get("reason","witness")
            if result["status"]=="FOUND":
                q=result["vertices"]
                assert len(q)==193 and not defects(q) and set(q[p::2])==edited
                witnesses.append(dict(change=[a,b,x,y],vertices=q))
                print("WITNESS",p,a,b,x,y,flush=True)
        stats[reason]+=1
        details.append([a,b,x,y,reason])
    row=dict(parity=p,first=start,last=end,require_removed_small_component=core,
             cases=int(tests),degree_pass=int(degree),connected_degree_pass=int(conn),
             downstream=stats,details=details,witnesses=witnesses)
    save(fname,row)
    print(fname,row["cases"],degree,conn,stats,flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("parity",type=int,choices=(0,1))
    parser.add_argument("start",type=int)
    parser.add_argument("end",type=int)
    parser.add_argument("--core",action="store_true")
    parser.add_argument("--exe",type=Path,default=Path("two-parity.exe"))
    a=parser.parse_args()
    check(a.parity,a.start,a.end,a.core,a.exe.resolve())
