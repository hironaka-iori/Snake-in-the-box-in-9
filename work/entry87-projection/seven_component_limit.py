"""Verify the 116-vertex bound for eight-cube forests with at most seven paths."""
import argparse
import json
from collections import Counter
from pathlib import Path

from dense_face_catalogue import list_classes
from forest_orbit_weights import bound
from variable_facet_weights import solve as template_bound
from solve import save


def verify(replay):
    census = json.loads(Path("dense-facet-audit.json").read_bytes())
    assert all(census[str(n)]["excluded"] == census[str(n)]["classes"] == count
               for n, count in ((62, 192), (63, 18), (64, 6)))
    caps = {}
    for i in range(6):
        file = Path(f"variable-facet-{i}-61-3.json")
        record = json.loads(file.read_bytes())
        assert (record["template"], record["lower_size"], record["upper_size"]) == (i, 61, 56)
        if replay:
            assert record == template_bound(i, 61, 3, record["certificate"])
        caps[i] = record["edge_upper"]
    assert max(caps.values()) < 110
    rows = list_classes(61)
    weights = Counter()
    counts = Counter()
    exceptions = []
    for i, row in enumerate(rows):
        family = row["full_class"]
        counts[family] += 1
        weights[family] += row["labelled"]
        if family >= 0:
            continue
        file = Path(f"individual-weight-61-{i}.json")
        proof = json.loads(file.read_bytes())
        assert (proof["fixed"], proof["size"]) == (row["forest"], 117)
        if replay:
            assert proof == bound(set(row["forest"]), 117, proof["certificate"])
        assert proof["max_edges"] < 104
        exceptions.append(dict(index=i, upper=proof["max_edges"], evidence=file.name))
    assert len(rows) == 1630 and len(exceptions) == 37 and sum(weights.values()) == 397775616
    # In each remaining coordinate cut the face populations are either 57+60
    # or 58+59. Their minimum component counts sum to 21 in either case.
    profile = json.loads(Path("face-component-bound.json").read_bytes())["seven_min_components"]
    pairs = [(n, 117-n) for n in range(57, 59)]
    face_component_sum = 8 * min(profile[str(a)] + profile[str(b)] for a, b in pairs)
    maximum_sum = 117 + 7 * 7
    assert face_component_sum == 168 > maximum_sum == 166
    return dict(template_edge_bounds=caps, shapes=counts, labelled=weights, exceptions=exceptions,
                face_component_sum_at_least=face_component_sum, face_component_sum_at_most=maximum_sum,
                maximum_vertices_with_at_most_seven_paths=116,
                maximum_nine_cube_snake_edges_with_thirteen_crossings=2*116-1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    result = verify(parser.parse_args().replay)
    save(Path("seven-component-limit.json"), result)
    print(result["face_component_sum_at_least"], result["face_component_sum_at_most"],
          result["maximum_nine_cube_snake_edges_with_thirteen_crossings"])
