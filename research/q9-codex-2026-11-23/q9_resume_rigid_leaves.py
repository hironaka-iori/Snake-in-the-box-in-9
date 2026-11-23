"""Replay each rigid-donor case and resume precisely the open leaves using prefix assignments."""
from pathlib import Path
import json,re,subprocess
from q9_check_rigid_tables import check
from q9_rigid_witnesses import decode
D=Path("q9_other_rigid_donors")
B=Path("q9_facet_priced_tree_20261121")
OUT=Path("q9_rigid_continuations")
def replay(tag,tree,pins=None):
    cmd=[str(B/"replay"),str(tag.with_suffix(".tables")),str(tree),"193"]
    if pins is not None:cmd.append(str(pins))
    out=subprocess.check_output(cmd,text=True)
    assert out.startswith("VERIFIED ")
    return {k:int(v) for k,v in re.findall(r"(\w+) (\d+)",out)}
def open_nodes(tree):
    with tree.open() as f:
        def go(prefix):
            h,*data=next(f).split()
            if h=="O": yield prefix
            elif h=="S":
                vertex=int(data[0]);assert all(x!=vertex for x,_ in prefix)
                for state in (0,1):yield from go(prefix+[(vertex,state)])
            else:assert h in ("B","H","F")
        yield from go([])
        assert f.readline()==""
def main():
    OUT.mkdir(exist_ok=True)
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    todo=[]
    for i,w in enumerate(bank):
        p=decode(w)
        if not any(v not in p and all((v^x).bit_count()!=1 for x in p[1:-1]) for v in range(256)):todo.append(i)
    old=json.loads(Path("q9_record_donor_optima.json").read_text())
    assert len(todo)==41 and all(old[str(i)]["conditional_optimum"]==191 for i in todo if str(i) in old)
    work=[]
    for i in todo:
        if str(i) in old:continue
        raw=D/f"donor{i}.jsonl";p=decode(bank[i]);assert len(p)==97 and p[0]==0
        needed={((0,),0),((p[-1],),0),((0,p[-1]),0),((0,p[-1]),1)}
        for line in raw.read_text().splitlines():
            r=json.loads(line);ports=tuple(r["ports"]);m=r["majority"];needed.remove((ports,m));assert r["word"]==bank[i]
            tag=D/("d%d_m%d_p%s"%(i,m,"-".join(map(str,ports))))
            tableopts,_=check(r,tag,[])
            tree=tag.with_suffix(".tree");initial=replay(tag,tree)
            jobs=list(open_nodes(tree)) if initial["open"] else []
            assert len(jobs)==initial["open"]
            print(json.dumps(dict(i=i,tag=tag.stem,initial=initial,table_assignments=tableopts)),flush=True)
            for j,prefix in enumerate(jobs):work.append((i,tag,j,prefix))
        assert not needed
    for i,tag,j,prefix in work:
        out=OUT/(tag.stem+"_leaf"+str(j));pins=out.with_suffix(".pins");tree=out.with_suffix(".tree")
        trace="".join(f"{v} {b}\n" for v,b in prefix)
        if pins.exists():assert pins.read_text()==trace
        pins.write_text(trace)
        if not tree.exists():
            tmp=out.with_suffix(".partial")
            subprocess.run([str(B/"tree"),str(tag),str(tmp),"193","1800000",str(pins)],capture_output=True,check=True)
            tmp.replace(tree)
        result=replay(tag,tree,pins)
        print(json.dumps(dict(i=i,tag=tag.stem,leaf=j,depth=len(prefix),verified=result)),flush=True)
        if result["witnesses"]:return
if __name__=="__main__":main()
