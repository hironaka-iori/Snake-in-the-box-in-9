"""Check the 95-edge case split, archive coverage, upper tables and branch tree replay."""
from pathlib import Path
import subprocess
import json
from q9_check_rigid_tables import check
from q9_classify_record_donor_windows import canonical
from q9_verify_one_hole_prices import options
from q9_rigid_facet_ports import word_path

def main():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    word=bank[472];core=word_path(word)[1:];low=set(core)
    adjacent=lambda v,w:(v^w).bit_count()==1
    eligible={v for v in range(256) if v not in low and not any(adjacent(v,w) for w in core[1:-1])}
    assert eligible=={0,33}
    extensions={}
    for x in sorted(eligible):
        assert [w for w in core if adjacent(w,x)]==[core[0]]
        key=canonical(str((x^core[0]).bit_length()-1)+word[1:])
        index,=[i for i,w in enumerate(bank) if canonical(w)==key]
        extensions[x]=index
    prev=json.loads(Path("q9_record_donor_optima.json").read_text())
    assert set(extensions.values())=={472,576} and all(prev[str(i)]["conditional_optimum"]==191 for i in extensions.values())
    archive=Path("q9_far189_spring_20261121/comparison191.words").read_text().split()
    matches=[i for i,w in enumerate(archive) if any(canonical(w[j:j+95])==canonical(word[1:]) for j in range(len(w)-94))]
    witnesses=[r["vertices"] for s in Path("q9_rigid_puncture_archive_20261121/hits.jsonl").read_text().splitlines() if (r:=json.loads(s))["donor"]==472 and r["hole"]==0 and {v for v in r["vertices"] if v<256}==low]
    assert witnesses
    for q in witnesses:
        assert len(q)==len(set(q))==192 and all(((v^u).bit_count()==1)==(j+1==k) for k,v in enumerate(q) for j,u in enumerate(q[:k]))
    d=Path("q9_frequent_95_core")
    pending={k for k,L in options(word,0,192) if L==low}
    assert len(pending)==4
    bounds={}
    for path in sorted(d.glob("*.json")):
        if not path.with_suffix(".tables").exists():continue
        r=json.loads(path.read_text())
        branch=((),tuple(r["ports"]),tuple(r["upper_endpoint_counts"]),r["upper_delta"])
        assert branch in pending and set(r["lower_vertices"])==low
        n,positive=check(r,path,witnesses[0])
        result=dict(local_assignments=n,positive_subpaths=positive,integer_root=r["total_scaled"],scale=r["cert"]["scale"])
        if r["total_scaled"]<193*r["cert"]["scale"]:
            pending.remove(branch)
        tree=path.with_suffix(".tree")
        if tree.exists() and path.stem+" VERIFIED" in Path("q9_frequent_95_core.log").read_text():
            replay=subprocess.check_output(["q9_facet_priced_tree_20261121/replay",str(path.with_suffix(".tables")),str(tree),"193"],text=True).strip()
            result["replay"]=replay
            if " open 0 witnesses 0 " in replay: pending.discard(branch)
        bounds[path.stem]=result
    print(json.dumps(dict(core_word=word[1:],extensions=extensions,record_ids=matches,real_191_witnesses_checked=len(witnesses),branches=bounds,remaining=len(pending)),indent=2))
if __name__=="__main__":main()
