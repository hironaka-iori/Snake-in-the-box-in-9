"""Match each feasible rooted pair in the grown menu to its unrestricted arm decision."""
import argparse
import json
from pathlib import Path
from solve import save


def audit(suffix, budget):
    menu = json.loads(Path(f"recombined-central{suffix}-menu.json").read_bytes())
    decisions = []
    capacity = 0
    for i, row in enumerate(menu["rows"]):
        if row["available"] < row["needed"]:
            capacity += 1
            continue
        tag = f"mix{suffix}-{i}"
        source = Path(f"three-central-{tag}-193-{budget}.json")
        r = json.loads(source.read_bytes())
        assert r["middle"] == row["middle"] and r["target"] == 193
        assert r["index"] == tag and r["domains"] == row["component_sizes"]
        assert r["status"] == "UNSAT" and r["witness"] is None
        decisions.append(dict(index=i, domains=r["domains"], conflicts=r["stats"]["conflicts"]))
    return dict(forms=len(menu["forms"]),placements=menu["counts"]["indexed"],
                compatible_placements=menu["counts"]["compatible"], known=menu["known"],
                alternatives=len(menu["rows"]), excluded_by_capacity=capacity,
                target_vertices=193, unsatisfiable=len(decisions), decisions=decisions)


if __name__ == "__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--grow-only",action="store_true")
    a=p.parse_args()
    suffix,budget=("-grow",250000) if a.grow_only else ("-1-1-grow",350000)
    result=audit(suffix,budget)
    save(Path(f"central{suffix}-decisions.json"),result)
    print(result["alternatives"],result["excluded_by_capacity"],result["unsatisfiable"])
