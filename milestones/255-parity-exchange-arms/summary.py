"""Reconcile the completed enumerations, rooted exclusions and explicit constructions."""
from collections import Counter
from pathlib import Path
import json
import sys
from enumerate_arms import HERE, PREVIOUS, SEED, digest
sys.path.insert(0, str(HERE.parent / "251-eighty-edge-segments"))
from bank_capacity import check_path


def main():
    pins = {}
    def read(file):
        pins[file.relative_to(HERE.parents[1]).as_posix()] = digest(file)
        return json.loads(file.read_bytes())
    geometry = read(HERE/"geometry.json")
    first = read(HERE/"arms.json")
    closure = read(HERE/"closure-replay.json")["closures"]
    extensions = read(HERE/"extension-boundary.json")["components"]
    focus = read(HERE/"focus-closure.json")
    six = read(HERE/"attainer-closure.json")
    new = set(first["outside_previous"])
    replay = read(HERE/"shared-proofs"/"partner-replay-95.json")
    direct = read(HERE/"partner-replay-95.json")
    cuts = read(HERE/"shared-proofs"/"cases.json")
    base = read(HERE/"partner-caps.json")
    if (replay["ledger_sha256"] != digest(HERE/"shared-proofs"/"cases.json")
            or direct["ledger_sha256"] != digest(HERE/"partner-caps.json")
            or {(r["shape"],r["end"],r["status"]) for r in replay["roots"]}
            != {(k,e,"excluded") for k in new for e in (0,1)}):
        raise ValueError("Unverified endpoint")
    if not all(r["partner_edges"] == 95 and first["shapes"][r["shape"]][0 if r["end"]==0 else -1] == r["root"]
               for r in replay["roots"]):
        raise ValueError("Wrong rooted domain")
    proof_counts = [sum(row["status"]=="excluded" for entry in d["roots"].values() for row in entry["95"])
                    for d in (base,cuts)]
    pool = read(HERE/"pool-replay.json")
    joins = read(HERE/"pool-joins.json")
    constructed = read(HERE/"constructive.json")
    if len(joins["cases"])!=528 or pool["shapes"]!=72 or geometry["compared_paths"]!=8:
        raise ValueError("Wrong scope")
    for row in [*joins["cases"].values(),*constructed["cases"].values()]:
        p, q = row["parent"], row["partner"]
        if p[0]!=0 or q[0]!=0 or set(p)&set(q)!={0} or row["joined"]!=p[::-1]+[x+256 for x in q]:
            raise ValueError("Invalid crossing")
        if len(row["joined"])-1!=row["joined_edges"]:
            raise ValueError("Wrong witness length")
        check_path(row["joined"],9)
    for label, keys in (("all",{r["shape"] for r in joins["cases"].values()}),
                        ("five_attainers_closure",set(six["paths"])),("round254_seed_closure",set(focus["paths"]))):
        rows=[r for r in joins["cases"].values() if r["shape"] in keys]
        if Counter(r["joined_edges"] for r in rows)!=Counter({int(k):v for k,v in joins["maxima"][label]["histogram"].items()}):
            raise ValueError("Placement histogram differs")
    known_closed = set(closure["focus"]["prior_excluded"]) | new
    left = sorted(set(focus["paths"])-known_closed)
    overlap = sorted(k for k,v in focus["expanded"].items() if set(v["outgoing"])<=known_closed)
    if overlap!=[SEED] or set(first["shapes"])-known_closed or any(paths for rows in extensions.values() for paths in rows.values()):
        raise ValueError("Overlap or extension claim fails")
    witness=read(HERE.parents[1]/"outputs"/"snake9_witness.json")
    n=check_path(witness["vertex_sequence"],9)
    if witness["edges"]!=191 or len(witness["vertex_sequence"])!=192 or n!=18336:
        raise ValueError("Global lower witness differs")
    inventory = first["known_shapes"] + len(closure["focus"]["outside_previous"])
    result = dict(round=255,pins=pins,global_witness_edges=191,global_witness_pairs_checked=n,
                  global_upper_from_contributor=230,independent_global_upper_rebuild=False,
                  inventory=inventory,previous_excluded=89,new_excluded=sorted(new),
                  open_inventory_shapes=inventory-89-len(new),open_focus_shapes=left,
                  references_for_46_overlap=sorted(set(six["paths"])|set(overlap)),
                  proof_archives_direct_and_transferred=proof_counts,
                  direct_family_witness=max(r["joined_edges"] for r in constructed["cases"].values()),
                  partner_pool_maxima={k:r["joined_edges"] for k,r in joins["maxima"].items()})
    (HERE/"summary.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
    print("Root exclusions",proof_counts,"open in inventory",result["open_inventory_shapes"],"open in focus",len(left),
          "overlap references",len(result["references_for_46_overlap"]))


if __name__ == "__main__":
    main()
