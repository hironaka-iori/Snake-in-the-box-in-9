"""Decide the fixed faces still open in an edge-incidence audit."""
import argparse
import json
from pathlib import Path

from dense_face_catalogue import list_classes
from dense_eight import facet_completion
from edge_rich_faces import read_shapes


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("report", type=Path)
    parser.add_argument("--budget", type=int, default=750000)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int)
    parser.add_argument("--checker", type=Path)
    parser.add_argument("--stop-at-witness", action="store_true")
    parser.add_argument("--highest-bound", action="store_true")
    args = parser.parse_args()
    report = json.loads(args.report.read_bytes())
    size = report["size"]
    limit = size-report["excluded_edge_target"]
    deletion = json.loads(Path("seven-deletion-classes.json").read_bytes())
    sixty_one = list_classes(61)
    other = {}
    pending=report["open_cases"]
    if args.highest_bound:
        def ceiling(case):
            n,i=case
            prefix="forest-role-weight" if n>=62 else "individual-weight"
            file=Path(f"{prefix}-{n}-{i}.json")
            if not file.exists():return float("inf")
            record=json.loads(file.read_bytes());cert=record["certificate"]
            return (record["numerator"]+(size-117)*cert["per_vertex"])/cert["scale"]
        pending=sorted(pending,key=ceiling,reverse=True)
    for n, i in pending[args.start:args.stop]:
        if n >= 62:
            vertices = deletion[str(n)][i]["forest"]
        elif n == 61:
            vertices = sixty_one[i]["forest"]
        else:
            if n not in other:
                minimum = report["minimum_face_edges"]
                other[n] = {j:vs for j,vs,_ in read_shapes(n,minimum)}
            vertices = other[n][i]
        tag = f"population{size}-{n}-{i}-{limit}-{args.budget}"
        checker = args.checker.resolve() if args.checker else None
        if checker:
            tag += "-checked"
        file = Path(tag+".json")
        if file.exists():
            record = json.loads(file.read_bytes())
            assert record["fixed"] == vertices and record["size"] == size
        else:
            record = facet_completion(vertices,size,limit,args.budget,tag,checker,True)
        if args.stop_at_witness and record["status"] == "FOUND":
            break
