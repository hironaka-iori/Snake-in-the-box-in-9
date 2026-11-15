"""Transport integer weight bounds to other face populations and bound dense Q8 forests."""
import argparse
import json
from pathlib import Path

from seven_component_limit import verify
from solve import save


def calculate(replay):
    base = verify(replay)
    sizes = json.loads(Path("forest-edge-bound.json").read_bytes())["occupancies"]
    seven = json.loads(Path("face-component-bound.json").read_bytes())["seven_min_components"]
    assert all(n - seven[str(n)] == 48 for n in range(57, 65))
    templates = [json.loads(Path(f"variable-facet-{i}-61-3.json").read_bytes()) for i in range(6)]
    exceptional = [json.loads(Path(x["evidence"]).read_bytes()) for x in base["exceptions"]]
    coverage = json.loads(Path("dense-seven-rigidity.json").read_bytes())
    records = []
    for m in range(117, 121):
        by_face = []
        for n in range(61, 65):
            caps = []
            for record in templates:
                cert = record["certificate"]
                # Each local pattern still omits at most three sites of the template.
                # Its block score is bounded by the same maximum; only the two
                # globally fixed population contributions change.
                numer = record["numerator"] + (n-61)*cert["lower"] + (m-n-56)*cert["upper"]
                caps.append(numer // cert["scale"])
            other = []
            if n == 61:
                for record in exceptional:
                    cert = record["certificate"]
                    numer = record["numerator"] + (m-117)*cert["per_vertex"]
                    other.append(numer // cert["scale"])
            else:
                assert coverage["populations"][str(n)]["outside_half_full"] == 0
            assert max(caps + other) < 110
            by_face.append(dict(population=n, template_bounds=caps, exceptional_max=max(other, default=None)))
        records.append(dict(vertices=m, dense_facets=by_face))
    # If a forest has 110 edges, incidence counting forces a face with at
    # least 49 edges. The opposite face then has m-56 or more vertices.
    assert 7*110 > 16*48
    upper = {r["vertices"]: r["edge_bound"] for r in sizes}
    for r in records:
        upper[r["vertices"]] = min(109, upper[r["vertices"]])
    assert all(v <= 109 for m, v in upper.items() if m >= 117)
    def capacity(components):
        return max(m for m, bound in upper.items() if m-bound <= components)
    assert (capacity(7), capacity(8)) == (116, 117)
    return dict(by_population=records, uniform_edge_upper_at_117_or_more=109,
                capacities={str(c): capacity(c) for c in range(6, 11)},
                maximum_edges_with_14_crossings=capacity(7)+capacity(8)-1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    result = calculate(parser.parse_args().replay)
    save(Path("dense-edge-profile.json"), result)
    print(result["capacities"], result["maximum_edges_with_14_crossings"])
