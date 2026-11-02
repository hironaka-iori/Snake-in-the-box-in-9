"""Reproduce the independent numeric review without overwriting saved evidence.

Provenance
----------
Recovered from /root/history_window84's two inline Python executions on
2026-11-03 (Japan time), recorded in the Codex task history. The first execution
independently checked the arrays, witnesses, weights, potentials, and arithmetic;
the second additionally checked source-model metadata agreement and clarified
the defined-graph scope. No standalone script existed during those executions.

This file preserves those computations and combines the two report-finalization
steps. Changes are limited to a reusable main function, CLI output handling,
local variable names, readable formatting, and this provenance note. It does not import or execute the
original extraction/BFS implementation.

The reviewed original JSON has SHA-256:
6fea38c92d9eedb7f69b4a5ceb4a6053cddca261e416b241b1cf643ad18beefe

Default: write a NEW timestamped reproduction JSON under ../data.
--output PATH: use a different NEW file, opened exclusively.
Existing files and the original reviewed JSON/reports cannot be overwritten.
The timestamp changes between reproductions, so byte-identical JSON is not
expected; the mathematical results and pinned evidence should agree.

Saving this implementation did not rerun the numerical review. Its Python
syntax was checked separately; the computations previously passed inline.
"""

from pathlib import Path
from fractions import Fraction
import argparse
import datetime
import gzip
import hashlib
import json
import sys


def main():
    here = Path(__file__).resolve().parents[1]
    repo = here.parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        help="New reproduction JSON path; existing files are never overwritten.",
    )
    args = parser.parse_args()
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output = (
        args.output if args.output is not None
        else here / "data" / f"range-certificate-review-reproduced-{stamp}.json"
    ).resolve()
    protected = {
        (here / "data/range-certificate-review.json").resolve(),
        (here / "audit/range-certificate-review.md").resolve(),
        (here / "audit/weight-bridge-plan.md").resolve(),
    }
    if output in protected or output.exists():
        parser.error(f"Refusing to overwrite saved evidence or an existing file: {output}")
    if not output.parent.is_dir():
        parser.error(f"The output directory must already exist: {output.parent}")

    sys.path.insert(0, str(repo / "work/solver_packages"))
    import numpy as np

    def sha(raw):
        return hashlib.sha256(raw).hexdigest()

    def read(path):
        return json.loads(path.read_text(encoding="utf-8-sig"))

    def pinfile(path):
        return sha(path.read_bytes())

    old = repo / "milestones/72-four-count-proof-closure/critical-current"
    source = read(old / "data/source-proved-model.json")
    with np.load(old / "build/source-graph.npz") as archive:
        arrays = {key: archive[key] for key in source["arrays_sha256"]}
    assert all(
        sha(arrays[key].tobytes()) == value
        for key, value in source["arrays_sha256"].items()
    )
    size = len(arrays["U"])
    assert size == 4947008
    model59 = read(repo / "milestones/59-extended-share-window/extended/data/model.json")
    words = model59["extensions"]
    shapes = model59["direction_shapes"]
    geometry = read(repo / "milestones/59-extended-share-window/data/geometry.json")["patterns"]
    history = read(repo / "milestones/67-critical-family-charge/data/full-model.json")
    prefixes = history["prefixes"]
    patterns = history["patterns"]
    dag_path = repo / "milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz"
    dag = json.loads(gzip.decompress(dag_path.read_bytes()))
    blocks = dict(dag["blocks"])
    assert len(blocks) == 791 and len(dag["roots"]) == 127

    def canonical(sequence):
        seen = []
        result = []
        for symbol in sequence:
            if symbol not in seen:
                seen.append(symbol)
            result.append(seen.index(symbol))
        return tuple(result)

    def symbols(code):
        result = [0] * 6
        for index in range(5, -1, -1):
            result[index] = code % 6 + 1
            code //= 6
        assert code == 0
        return result

    def diagram(direction, hist, code):
        assert 0 <= direction < 505 and 0 <= hist < 75 and 0 <= code < 46656
        cls = blocks[75 * direction + hist]
        node = dag["roots"][cls]
        route = [node]
        for remaining, symbol in zip(range(6, 0, -1), symbols(code)):
            if node not in (0, 1):
                row = dag["nodes"][node - 2]
                assert len(row) == 7 and row[0] == remaining
                node = row[symbol]
                assert 0 <= node < len(dag["nodes"]) + 2
            route.append(node)
        assert node == 1
        return cls, route

    forward = [
        ([0, 1, 2, 3, 1, 4], [3, 3, 3, 6, 5], 48),
        ([0, 1, 2, 3, 4, 5], [3, 6, 2, 3, 6], 96),
        ([0, 1, 2, 0, 3, 4], [6, 3, 6, 3, 3], 96),
        ([0, 1, 2, 3, 4, 5], [4, 6, 2, 3, 6], 96),
    ]
    rules = forward + [
        (canonical(word[::-1]), counts[::-1], value)
        for word, counts, value in forward
    ]
    shape_index = {tuple(word): index for index, word in enumerate(shapes)}

    def original_key_semantics(direction, hist, code):
        word = words[direction]
        counts = symbols(code)
        assert geometry[direction]["directions"] == word
        candidates = [geometry[direction]["share_lower"]]
        for rule_word, rule_counts, value in rules:
            if canonical(word[-6:]) == tuple(rule_word) and counts[1:] == rule_counts:
                candidates.append(value)
        emitted = prefixes[hist] + [direction]
        for row in patterns:
            if len(emitted) >= 3 and emitted[-3:] == row["signature"]:
                hit = all(counts[int(index)] <= cap for index, cap in row["caps"].items())
                if row["mode"] == "exclusion":
                    assert not hit
                else:
                    candidates.append(row["geometric_lower"])
                    if hit:
                        candidates.append(row["lower"])
        if (
            len(set(word[-6:])) == 6
            and counts[1:] in ([4, 5, 4, 2, 6], [6, 2, 4, 5, 4])
        ):
            candidates.append(120)
        options = [
            index for index, pref in enumerate(prefixes)
            if pref and len(pref) <= len(emitted) and emitted[-len(pref):] == pref
        ]
        next_hist = max(options, key=lambda index: len(prefixes[index])) if options else 0
        source_shape = shape_index[canonical(word[:8])]
        target_shape = shape_index[canonical(word[1:])]
        assert hist == 0 or history["compatible_shapes"][hist] == source_shape
        assert next_hist == 0 or history["compatible_shapes"][next_hist] == target_shape

        def state(shape, hist, count):
            return shape * 7776 + count if hist == 0 else 1026432 + (hist - 1) * 7776 + count

        return (
            120 * counts[-1] + max(candidates),
            state(source_shape, hist, code // 6),
            state(target_shape, next_hist, code % 7776),
        )

    common_inputs = {
        str(path.relative_to(repo)): pinfile(path)
        for path in [
            old / "data/source-proved-model.json",
            dag_path,
            repo / "milestones/59-extended-share-window/extended/data/model.json",
            repo / "milestones/59-extended-share-window/data/geometry.json",
            repo / "milestones/67-critical-family-charge/data/full-model.json",
            here / "scripts/extract_range_certificates.py",
        ]
    }
    results = []
    all_input_pins = {}
    witness_keys = set()
    for label in ["completed", "additional012034", "full-conditional"]:
        certificate_path = here / "data" / f"{label}-range-certificate.json"
        certificate = read(certificate_path)
        for relative, pin in certificate["input_sha256"].items():
            assert pinfile(repo / relative) == pin, relative
            all_input_pins[relative] = pin
        assert (
            pinfile(here / "scripts/extract_range_certificates.py")
            == certificate["script_sha256"]
        )
        assert certificate["arrays_sha256"] == source["arrays_sha256"]
        if label == "completed":
            model_path = repo / "milestones/73-countfree-share-catalogue/data/proved-model.json"
            potential_path = model_path.with_name("proved-potential.i64.gz")
        elif label == "additional012034":
            model_path = repo / "milestones/83-012034-share-certificate/data/assumed-012034x20-model.json"
            potential_path = model_path.with_name("assumed-012034x20-potential.i64.gz")
        else:
            stem = "countfree16-all-except012034x20-except012310x12"
            model_path = old / "data" / f"{stem}-model.json"
            potential_path = old / "data" / f"{stem}-potential.i64.gz"
        metadata = read(model_path)
        if label != "full-conditional":
            floors = {
                tuple(row["shape"]): row["share"] for row in metadata["countfree_floors"]
            }
        else:
            floors = {
                min(canonical(word), canonical(word[::-1])):
                    metadata["countfree_overrides"].get(
                        "".join(map(str, min(canonical(word), canonical(word[::-1])))),
                        metadata["countfree_share_lower"],
                    )
                for word in metadata["countfree_shapes"]
            }
        by_direction = np.array(
            [
                floors.get(min(canonical(word[-6:]), canonical(word[-6:][::-1])), 0)
                for word in words
            ],
            dtype=np.int64,
        )
        raw = gzip.decompress(potential_path.read_bytes())
        assert sha(raw) == certificate["potential_sha256"]
        potential = np.frombuffer(raw, dtype="<i8")
        assert len(potential) == 1601856
        mean = Fraction(certificate["mean"])
        numerator, denominator = mean.numerator, mean.denominator
        assert denominator == certificate["denominator"]
        potential_range = int(potential.max()) - int(potential.min())
        assert int(potential.min()) == 0
        assert potential_range == certificate["potential_range_scaled"]
        assert Fraction(certificate["potential_range"]) == Fraction(potential_range, denominator)
        output_hash = hashlib.sha256()
        minimum_slack = None
        tight = 0
        for first in range(0, size, 100000):
            last = min(size, first + 100000)
            interval = slice(first, last)
            count = arrays["count_code"][interval].astype(np.int64)
            weight = np.maximum(
                arrays["weight"][interval].astype(np.int64),
                120 * (count % 6 + 1) + by_direction[arrays["direction"][interval]],
            )
            output_hash.update(weight.astype("<i8", copy=False).tobytes())
            slack = (
                denominator * weight
                + potential[arrays["U"][interval]]
                - potential[arrays["V"][interval]]
                - numerator
            )
            current_minimum = int(slack.min())
            assert current_minimum >= 0
            minimum_slack = (
                current_minimum if minimum_slack is None
                else min(minimum_slack, current_minimum)
            )
            tight += int(np.count_nonzero(slack == 0))
        assert output_hash.hexdigest() == certificate["weight_sha256"]
        assert tight == certificate["tight_edges"]
        row_details = []
        for kind in ["path", "cycle"]:
            rows = certificate[kind]
            assert rows
            for index, row in enumerate(rows):
                edge = row["edge"]
                assert 0 <= edge < size
                direction, hist, code = [
                    int(arrays[key][edge]) for key in ["direction", "history", "count_code"]
                ]
                assert (direction, hist, code) == (
                    row["direction"], row["history"], row["count_code"]
                )
                source_vertex = int(arrays["U"][edge])
                target_vertex = int(arrays["V"][edge])
                assert (source_vertex, target_vertex) == (row["u"], row["v"])
                base, reconstructed_source, reconstructed_target = original_key_semantics(
                    direction, hist, code
                )
                assert (reconstructed_source, reconstructed_target) == (
                    source_vertex, target_vertex
                )
                assert base == int(arrays["weight"][edge])
                weight = max(base, 120 * (code % 6 + 1) + int(by_direction[direction]))
                assert weight == row["weight"]
                cls, route = diagram(direction, hist, code)
                assert cls == row["diagram_class"]
                assert (
                    int(potential[source_vertex]), int(potential[target_vertex])
                ) == (row["source_potential"], row["target_potential"])
                assert (
                    numerator + int(potential[target_vertex])
                    == denominator * weight + int(potential[source_vertex])
                )
                if index:
                    assert rows[index - 1]["v"] == source_vertex
                witness_keys.add((direction, hist, code))
                row_details.append([kind, edge, direction, hist, code, cls, route])
            if kind == "cycle":
                assert rows[-1]["v"] == rows[0]["u"]
        cycle_length = len(certificate["cycle"])
        cycle_weight = sum(row["weight"] for row in certificate["cycle"])
        path_length = len(certificate["path"])
        path_weight = sum(row["weight"] for row in certificate["path"])
        assert cycle_length == certificate["cycle_edges"]
        assert cycle_weight == certificate["cycle_weight"]
        assert Fraction(cycle_weight, cycle_length) == mean
        assert path_length == certificate["path_edges"]
        assert path_weight == certificate["path_weight"]
        assert (
            numerator * path_length - denominator * path_weight
            == potential_range == certificate["path_deficit_scaled"]
        )
        assert certificate["path"][0]["source_potential"] == potential_range
        assert certificate["path"][-1]["target_potential"] == 0
        bound = Fraction(
            1098960 * denominator + 8 * numerator + potential_range,
            4200 * denominator + numerator,
        )
        assert str(bound) == certificate["comparison_bound"]
        integer = bound.numerator // bound.denominator
        assert integer == certificate["comparison_integer_bound"]
        assert Fraction(integer) <= bound < Fraction(integer + 1)
        joint = 1098960 - path_weight - 4200 * (path_length + 8)
        margin = bound - (path_length + 8)
        assert joint >= 0
        assert margin == Fraction(joint, 1) / (4200 + mean)
        assert str(margin) == certificate["joint_condition_margin"]
        assert certificate["joint_slope_range_condition"]
        # Consistency checks only; the companion report gives the general algebra.
        for slope in [Fraction(0), mean / 3, mean / 2, mean - 1, mean]:
            lower = (1098960 - path_weight + (path_length + 8) * slope) / (4200 + slope)
            difference = (
                (mean - slope) * joint / ((4200 + slope) * (4200 + mean))
            )
            assert lower - bound == difference and difference >= 0
        result = dict(
            model=label,
            certificate_sha256=pinfile(certificate_path),
            mean=str(mean),
            scale=denominator,
            path_length=path_length,
            path_weight=path_weight,
            path_scaled_deficit=potential_range,
            cycle_length=cycle_length,
            cycle_weight=cycle_weight,
            raw_potential_min=0,
            raw_potential_max=potential_range,
            all_array_edges_checked=size,
            minimum_scaled_slack=minimum_slack,
            tight_edges=tight,
            full_key_occurrences_checked=len(certificate["path"]) + len(certificate["cycle"]),
            independent_witness_semantic_reconstruction=True,
            diagram_traversal_evidence_sha256=sha(
                json.dumps(row_details, separators=(",", ":")).encode()
            ),
            reconstructed_weight_sha256=output_hash.hexdigest(),
            raw_potential_sha256=sha(raw),
            comparison_bound=str(bound),
            comparison_integer=integer,
            next_integer_exclusion_margin=(
                (integer + 1) * (4200 * denominator + numerator)
                - (1098960 * denominator + 8 * numerator + potential_range)
            ),
            joint_condition_numerator=joint,
            joint_condition_margin=str(margin),
            shortest_path_claim_checked=False,
        )
        # Recovered from the second inline validation/finalization execution.
        if label == "full-conditional":
            assert metadata["arrays_sha256"]["weight"] == certificate["weight_sha256"]
            assert all(
                metadata["arrays_sha256"][key] == source["arrays_sha256"][key]
                for key in metadata["arrays_sha256"] if key != "weight"
            )
            analysis = read(model_path.with_name(
                model_path.name.replace("-model.json", "-analysis.json")
            ))
            assert str(analysis["integer_mean"]) == certificate["mean"]
            assert analysis["potential_range"] == certificate["potential_range_scaled"]
            assert analysis["potential_sha256"] == certificate["potential_sha256"]
        else:
            assert metadata["weight_sha256"] == certificate["weight_sha256"]
            assert metadata["mean"] == certificate["mean"]
            assert metadata["potential_range"] == certificate["potential_range_scaled"]
            assert metadata["potential_sha256"] == certificate["potential_sha256"]
        result["source_model_metadata_agreement"] = True
        results.append(result)
        print(
            label, "PASS", mean, "path", path_length, path_weight, potential_range,
            "comparison", bound, "integer", integer, flush=True,
        )
    report = dict(
        status="PASS_INDEPENDENT_NUMERIC_RANGE_CERTIFICATE_REVIEW",
        recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        models=results,
        unique_full_witness_keys=len(witness_keys),
        common_input_sha256=common_inputs,
        certificate_input_sha256=all_input_pins,
        source_arrays_sha256=source["arrays_sha256"],
        method=(
            "Independent Python implementation; no imports or execution of extraction/BFS "
            "functions. Reconstructed profile weights from pinned source arrays and declared "
            "floors, and independently reconstructed original witness weights and raw "
            "endpoints from geometric, history and count rules. Checked the complete "
            "potential arrays and all finite-array edge inequalities in 100000-edge chunks. "
            "Traversed the six-digit acceptance DAG for every listed full key. Used exact "
            "Fraction arithmetic for comparisons."
        ),
        scope=(
            "Finite weighted graphs only. No Lean compilation, no BFS, no shortest-path "
            "or search-minimality claim, and no actual-snake realization. All three "
            "cycle/path witnesses and their sharp fixed-slope range certificates pass. "
            "The fixed-boundary joint slope/range comparison is justified by the exact "
            "algebra documented in the companion report; pending local floors and the "
            "graph weight-to-share bridge remain outside this review. Full "
            "acceptance-diagram equality to the array graph was not re-proved: only the "
            "supplied witness keys were traversed in this review. Potential inequalities "
            "for possible additional defined-graph rows require their own coverage check."
        ),
    )
    # Exclusive creation also protects against a file appearing during computation.
    with output.open("x", encoding="utf-8", newline="\n") as destination:
        destination.write(json.dumps(report, indent=2) + "\n")
    print("Reproduction output:", output)
    print("Review SHA256", pinfile(output))


if __name__ == "__main__":
    main()
