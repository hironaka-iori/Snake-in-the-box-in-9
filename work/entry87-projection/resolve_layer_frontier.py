"""Decide all splits between the two independent rooted arms of a saved anchor pair."""
import argparse,json
from pathlib import Path
from free_last_drat import decide
from solve import defects,save


def trial(i,row,budget,checker):
    A=row["first"];C=row["third"];need=row["required_sum"];D={}
    def solve_arm(which,size):
        root=A[-1] if which=="middle" else C[-1];domain=row[which+"_domain"]
        tip=(C[0]^root) if which=="middle" else None
        r=decide([v^root for v in domain],size,budget,f"frontier-{i}-{which}-{size}",checker,tip)
        if r.get("path"):
            r["path"]=[v^root for v in r["path"]]
            assert r["path"][0]==root and (tip is None or r["path"][-1]==C[0]) and not defects(r["path"])
        return r
    eliminated={"UNSAT","parity","component","tip unreachable"};answers=[];out="EXHAUSTED";hit=None
    for b in range(row["middle_upper"],need-row["last_upper"]-1,-1):
        if (b-1)%2!=(A[-1]^C[0]).bit_count()%2:continue
        size=need-b
        if size not in D:D[size]=solve_arm("final",size)
        d=D[size];record=dict(middle_size=b,last_size=size,last=d);answers.append(record)
        if d["status"] in eliminated:break
        mid=solve_arm("middle",b);record["middle"]=mid
        if mid["status"] in eliminated:continue
        if mid.get("path") and d.get("path"):
            hit=A+[v|128 for v in mid["path"]]+[v|384 for v in C]+[v|256 for v in d["path"]]
            assert len(hit)==193 and not defects(hit);out="FOUND";break
        out="OPEN"
    return dict(index=i,status=out,splits=answers,vertices=hit)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=120000);p.add_argument("--proof",action="store_true")
    a=p.parse_args();inputs=json.loads(Path("one-layer-frontier.json").read_text())["cases"];rows=[]
    for i in range(a.first,min(a.stop,len(inputs))):
        r=trial(i,inputs[i],a.budget,Path("drat-check.exe").resolve() if a.proof else None);rows.append(r)
        save(Path(f"resolved-layer-{a.first}-{a.stop}-{a.budget}-{int(a.proof)}.json"),rows)
        if r["vertices"]:break
