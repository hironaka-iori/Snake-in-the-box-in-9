"""Reconcile shell replays, cube isometry, rooted exclusions and constructive witnesses."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"251-eighty-edge-segments"))
from bank_capacity import check_path
sys.path.insert(0,str(MS/"252-shorter-reference-segments"))
from replay_core import word

def load(f): return json.loads(f.read_bytes())
def digest(f): return sha256(f.read_bytes()).hexdigest()


def main():
    previous=MS/"255-parity-exchange-arms"
    summary256=MS/"256-two-exchange-parents/summary.json"
    six=set(load(summary256)["closure"])
    base=load(previous/"summary.json")
    cases=load(HERE/"replay.json")["shells"]
    all_six={}
    positives=[]
    for name,receipt in cases.items():
        p=HERE/name
        s=load(p)
        if receipt["sha256"]!=digest(p): raise ValueError("Replay source differs")
        if s["reference_shape"] in six:
            all_six[s["reference_shape"]]=s["counts"]
            for row in s["positive_classes"]:
                for v in row["paths"]:
                    positives.append((s,row,v))
    if set(all_six)!=six or len(positives)!=1: raise ValueError("Six-shape coverage disagrees")
    s,r,v=positives[0]
    def swap(x):
        return x ^ (96 if ((x>>5)^(x>>6))&1 else 0)
    image=list(map(swap,s["reference"]))
    if image!=v["vertices"] or v["shape"]!=s["reference_shape"] or check_path(image,8)!=4656:
        raise ValueError("Ordered isometry differs")
    two=load(HERE/"two-exchange-comparison/shell-distant.json")
    if digest(HERE/"two-exchange-comparison/shell-distant.json")!=load(
            HERE/"two-exchange-comparison/replay.json")["shells"]["shell-distant.json"]["sha256"]:
        raise ValueError("Radius-two replay differs")
    three=load(HERE/"shell-distant.json")
    first,second=set(two["shapes"]),set(three["shapes"])
    focus=set(load(previous/"focus-closure.json")["paths"])
    if len(first)!=14 or len(second)!=15 or first&second or first-focus or len(second-focus)!=2:
        raise ValueError("Distant geometry differs")
    all_paths=two["shapes"]|three["shapes"]
    extensions={}
    for key,path in all_paths.items():
        if sha256(word(path)).hexdigest()!=key: raise ValueError("Shape differs")
        extensions[key]=[]
        for order in [path,path[::-1]]:
            for i in range(8):
                candidate=order[-1]^(1<<i)
                if candidate not in order and all((candidate^old).bit_count()!=1 for old in order[:-1]):
                    extensions[key].append([order[-1],candidate])
    extended_paths=[]
    previous_97=MS/"252-shorter-reference-segments/replay-68-192.json"
    earlier=load(previous_97)
    for key,options in extensions.items():
        for tip,extra in options:
            p=all_paths[key]
            q=(p if tip==p[-1] else p[::-1])+[extra]
            check_path(q,8)
            shape=sha256(word(q)).hexdigest()
            records=[r for r in earlier["endpoints"] if r["id"]==shape]
            if len(q)!=98 or {r["end"] for r in records if r["status"]=="excluded" and r["shortest_excluded"]==192}!={0,1}:
                raise ValueError("Missing earlier exclusion at length 97")
            for order in (q,q[::-1]):
                for j in range(8):
                    y=order[-1]^(1<<j)
                    if y not in order and all((u^y).bit_count()!=1 for u in order[:-1]):
                        raise ValueError("An extension to 98 exists")
            extended_paths.append(dict(source=key,vertices=q,shape=shape,earlier_roots=records))
    if len(extended_paths)!=1: raise ValueError("Unexpected extension count")
    proof=load(HERE/"partner-replay-95.json")
    if proof["ledger_sha256"]!=digest(HERE/"partner-caps.json"): raise ValueError("Stale proof replay")
    selected=load(HERE/"partner-input.json")["outside_previous"]
    roots={(r["shape"],r["end"]):r for r in proof["roots"]}
    if set(roots)!={(k,e) for k in selected for e in range(2)}: raise ValueError("Missing selected roots")
    closed0=focus-set(base["open_focus_shapes"])
    closed={k for k in selected if all(roots[k,e]["status"]=="excluded" for e in range(2))}
    if any(r["status"]=="witness" for r in roots.values()): raise ValueError("A positive target needs review")
    closed_all=closed0|closed
    def coverage(keys):
        good=keys&closed_all
        return dict(total=len(keys),both_roots_excluded=sorted(good),unresolved=sorted(keys-good),
                    shapes_with_extensions=[k for k in sorted(keys) if extensions[k]])
    constructions={}
    for f in ["constructed.json","constructed-51.json"]:
        results=load(HERE/f)
        if set(results["cases"])!={k+":"+str(e) for k in all_paths for e in [0,1]}:
            raise ValueError("Partial constructive coverage")
        winners=[]
        for t,row in results["cases"].items():
            p=all_paths[row["shape"]]
            if row["end"]: p=p[::-1]
            p=[v^p[0] for v in p]
            candidate=p[::-1]+[256+y for y in row["partner"]]
            if candidate!=row["joined"] or check_path(candidate,9)!=row["all_pairs"]:
                raise ValueError("Constructive witness differs")
            if row["joined_edges"]==results["best_join"]: winners.append(t)
        viable=[r for r in results["cases"].values() if r["unrestricted_tail_max"] is not None]
        constructions[results["core_edges"]]=dict(maximum=max(97+r["unrestricted_tail_max"] for r in viable),
                roots_with_core=len(viable),placed_prefixes=results["ordered_placements"],winners=winners,
                ordered_prefixes=results["rooted_core_words"],tail_search_nodes=results["continuation_nodes"])
    witness_source=MS.parent/"outputs/snake9_witness.json"
    w=load(witness_source)["vertex_sequence"]
    if len(w)!=192 or check_path(w,9)!=18336: raise ValueError("Global witness differs")
    best_case=load(HERE/"constructed-51.json")["cases"][constructions[51]["winners"][0]]
    witness=dict(parent_shape=best_case["shape"],root_in_parent_labelling=best_case["original_root"],
                 target_family="51-edge rooted donor segment with arbitrary continuation",
                 vertices=best_case["joined"],edges=best_case["joined_edges"],pairs=best_case["all_pairs"],
                 transition_axes=[(x^y).bit_length()-1 for x,y in zip(best_case["joined"],best_case["joined"][1:])])
    (HERE/"best-join.json").write_text(json.dumps(witness,indent=2)+"\n",encoding="utf-8",newline="\n")
    result=dict(six_reference_three_exchange_candidates=sum(c["all_classes"] for c in all_six.values()),
                six_reference_overlap_ceiling=44,sole_three_exchange=dict(shape=v["shape"],
                deleted=r["removed"],inserted=r["inserted"],swapped_axes=[5,6]),
                distant_two=coverage(first),distant_three=coverage(second),escaped=sorted(second-focus),
                complete_one_edge_extensions=extended_paths,
                new_focus_closures=sorted(closed&set(base["open_focus_shapes"])),
                remaining_in_41_shape_component=sorted(set(base["open_focus_shapes"])-closed),
                explicitly_checked_95_partner_root_status=proof["counts"],constructions=constructions,
                global_bounds=[191,230],independent_upper_bound_rebuild=False,global_witness_pairs=18336,
                inputs={q.relative_to(MS.parent).as_posix():digest(q) for q in
                        [summary256,previous/"summary.json",HERE/"replay.json",HERE/"two-exchange-comparison/replay.json",
                         HERE/"constructed.json",HERE/"constructed-51.json",HERE/"partner-replay-95.json",
                         HERE/"contributor.json",HERE/"Supply257-compile.json",previous_97,witness_source,Path(__file__)]})
    (HERE/"summary.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
    print("95-edge roots",proof["counts"],"unresolved shapes at distance 2 and 3",
          len(first-closed_all),len(second-closed_all),"core maxima",constructions[51]["maximum"],constructions[72]["maximum"])

if __name__=="__main__": main()
