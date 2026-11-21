"""Enumerate continuations grouped by their first difference from a saved partner."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from construct254 import COMPILER, check_join

HERE=Path(__file__).resolve().parent
INPUTS=(("e6e522b8-0","parity-joins.json"),("6f8ef24c-161","constructive.json"))


def optimize(exe, row):
    seed=row["partner"]
    parent=row["joined"][:row["joined"].index(256)][::-1]
    if check_join(parent,seed)["joined"]!=row["joined"]: raise ValueError("Bad archived join")
    data="".join(",".join(map(str,p))+"\n" for p in (parent,seed))
    result=subprocess.run([str(exe)],input=data,text=True,capture_output=True,check=True,timeout=100)
    groups=[]; best=seed; all_closed=True; visited=0; shortest=None; longest_failure=None
    saved={}; original=len(seed)-1
    for line in result.stdout.splitlines():
        k,flag,n,vertices=line.split()
        k,complete,n=int(k),bool(int(flag)),int(n)
        if k!=original-len(groups): raise ValueError("Unexpected divergence group")
        arm=[int(v) for v in vertices.split(",")]
        if arm[:k+1]!=seed[:k+1] or (k<original and arm[k+1:k+2]==seed[k+1:k+2]):
            raise ValueError("Incorrect first-difference witness")
        check_join(parent,arm)
        if len(arm)>len(best): best=arm
        all_closed&=complete; visited+=n
        if all_closed and len(best)==len(seed): shortest=k
        if len(best)>len(seed) and longest_failure is None: longest_failure=k
        item=dict(frozen_edges=k,group_complete_and_independently_counted=complete,
                  group_visited=n,group_attained_edges=len(arm)-1,
                  maximum_if_complete_else_lower=len(best)-1,all_groups_complete=all_closed)
        if all_closed: item["exact_prefix_tree_size"]=visited
        if len(arm)>len(seed):
            item["longer_partner_key"]=str(k)
            saved[str(k)]=arm
        groups.append(item)
    if not groups or groups[-1]["frozen_edges"]!=8: raise ValueError("Incomplete cutoff sequence")
    return dict(id=row["id"],root=row["root"],initial_partner_edges=original,
                shortest_verified_optimal_prefix=shortest,
                longest_prefix_with_longer_witness=longest_failure,
                shortest_optimal_prefix_interval=[0 if longest_failure is None else longest_failure+1,shortest],
                groups=groups,longer_partners=saved,**check_join(parent,best))


def main():
    native=HERE/"Prefix254.cs"
    inputs=[HERE/f for _,f in INPUTS]+[native,Path(__file__),HERE/"construct254.py",
            HERE.parent/"252-shorter-reference-segments"/"construct.py",
            HERE.parent/"251-eighty-edge-segments"/"bank_capacity.py"]
    pins={p.name:sha256(p.read_bytes()).hexdigest() for p in inputs}
    target=HERE/"prefix-optima.json"
    data=json.loads(target.read_bytes()) if target.exists() else dict(pins=pins,cases={})
    if data["pins"]!=pins: raise ValueError("Inputs changed between completed cases")
    with TemporaryDirectory() as folder:
        exe=Path(folder)/"Prefix254.exe"
        subprocess.run([str(COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(native)],
                       check=True,capture_output=True)
        for key,file in INPUTS:
            if key in data["cases"]: continue
            r=json.loads((HERE/file).read_bytes())["cases"][key]
            result=optimize(exe,r)
            data["cases"][key]=result
            tmp=target.with_suffix(".tmp")
            tmp.write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8",newline="\n")
            tmp.replace(target)
            print(key,result["initial_partner_edges"],result["partner_edges"],result["joined_edges"],
                  result["shortest_optimal_prefix_interval"],flush=True)


if __name__=="__main__":main()
