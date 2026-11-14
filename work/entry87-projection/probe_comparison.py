"""Paired comparison of round 215's solver with and without the 57 root deductions."""
import argparse
from itertools import combinations
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from parent_triples import get, sha256, STATE
from solve import save


def assemble(x,bits):
    return sum(((x>>k)&1)<<p for k,p in enumerate(bits))


def validate(model,perms,root,result):
    v=result["solution"]
    assert all(d>>w&1 for d,w in zip(root,v)) and v not in model["nogoods"]
    assert all(c["rows"][v[c["x"]]]>>v[c["y"]]&1 for c in model["constraints"])
    assert all(tuple(v)<=tuple(p[w] for w in v) for p in perms)
    path=[assemble(z,model["base"])|assemble(v[g],model["block"])
          for z,g in zip(model["z"],model["group"])]
    assert len(path)==99 and all(0<=x<256 for x in path)
    for i,j in combinations(range(len(path)),2):
        d=(path[i]^path[j]).bit_count()
        assert d==1 if j==i+1 else d>=2
    return path


def compare(compiler,node_limit,out):
    state_raw=get("data/case-22/state.json")
    assert sha256(state_raw).hexdigest()==STATE
    state=json.loads(state_raw)
    inputs={k:get("data/case-22/"+k) for k in ("model.json","permutations.json","input-tail.txt")}
    assert all(sha256(v).hexdigest()==state["model_pins"][k] for k,v in inputs.items())
    model=json.loads(inputs["model.json"])
    perms=json.loads(inputs["permutations.json"])
    full=get("scripts/word_solver.c")
    assert sha256(full).hexdigest()==state["engine_pins"]["scripts\\word_solver.c"]
    experiment=json.loads(Path("parent-triples-215.json").read_text())
    assert experiment["state_sha256"]==STATE
    exclusions={r["region"]:r["singleton_rejections"] for r in experiment["regions"]}
    result=dict(state_sha256=STATE,node_budget=node_limit,runs=[])
    with TemporaryDirectory() as tmp:
        work=Path(tmp)
        src=work/"solver.c";src.write_bytes(full);exe=work/"solver.exe"
        subprocess.run([str(compiler),"-O2",str(src),"-o",str(exe)],check=True)
        for idx,region in enumerate(state["frontier"]):
            masks=region["domains"]
            tests=[False,True] if idx%2==0 else [True,False]
            for filtered in tests:
                root=masks.copy()
                if filtered:
                    for i,w in exclusions[region["id"]]:
                        assert root[i]>>w&1
                        root[i]&=~(1<<w)
                assert all(root)
                head=(f'{len(root)} 64 {len(model["constraints"])} {len(model["nogoods"])} {len(perms)}\n'
                      + f'3600 {node_limit}\n'+" ".join(map(str,root))+"\n").encode()
                data=head+inputs["input-tail.txt"]
                p=subprocess.run([str(exe)],input=data,capture_output=True,check=True,cwd=work)
                row=json.loads(p.stdout)
                if row["status"]=="FOUND":
                    row["vertices"]=validate(model,perms,root,row)
                assert row["status"] in ("LIMIT","FOUND","EXHAUSTED")
                row["input_sha256"]=sha256(data).hexdigest()
                row["pending_count"]=len(row.pop("pending"))
                row.update(region=region["id"],preprobe=filtered)
                result["runs"].append(row)
                save(out,result)
                print(region["id"],filtered,row["status"],row["nodes"],row["seconds"],flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--cc",required=True,type=Path)
    parser.add_argument("--nodes",type=int,default=250000)
    parser.add_argument("--output",type=Path,default=Path("parent-probe-comparison.json"))
    args=parser.parse_args()
    compare(args.cc.resolve(),args.nodes,args.output)
