"""Independently compare retained count-code lists; never modify source arrays.
No weight construction, solver, Lean invocation, or historical builder execution.
"""
from pathlib import Path
import collections
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "work/solver_packages"))
import numpy as np

START = time.monotonic()
PINS = {}
REPORT = {
    "status": "RUNNING",
    "scope": "Computational equality of exact retained count-code lists, using current pinned inputs. No Lean finite-array equality or global snake theorem is claimed.",
}
OUT = HERE / "data/retention-equality.json"


def digest_file(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_json(relative):
    path = ROOT / relative
    raw = path.read_bytes()
    PINS[relative] = hashlib.sha256(raw).hexdigest()
    return json.loads(raw.decode("utf-8-sig"))


def canonical(word):
    labels = {}
    return tuple(labels.setdefault(x, len(labels)) for x in word)


def encode(symbols):
    value = 0
    for x in symbols:
        value = 6 * value + int(x) - 1
    return value


def main():
    sm = load_json("milestones/59-extended-share-window/extended/data/model.json")
    md = load_json("milestones/67-critical-family-charge/data/full-model.json")
    saved = load_json("milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json")
    enriched = load_json("milestones/70-proof-supported-share-model/data/enriched-model.json")
    count_cases = load_json("milestones/72-four-count-proof-closure/data/cases.json")
    count_audit = load_json("milestones/72-four-count-proof-closure/data/proof-audit.json")
    ref235 = load_json("milestones/54-share-coverage/data/keys_235.json")["keys"]
    ref236 = load_json("milestones/39-audited-bound-236/data/exclusion-catalogue.json")
    short = []
    for family in ["47-critical-singleton-patterns", "48-low-count-compatibility", "49-six-direction-pair-catalogue"]:
        short += [dict(row, source=family) for row in load_json(f"milestones/{family}/data/cases.json")]
    short.append(dict(number=501, source="50-three-count-return", dirs=[0, 1, 2, 3, 4, 0], positions=[1, 4, 5], kind="sum", cap=12))
    assert short == enriched["additional_proved_rules"] and len(short) == 40
    assert md["prefixes"] == enriched["prefixes"]
    assert md["compatible_shapes"] == enriched["compatible_shapes"]
    assert md["patterns"] == enriched["patterns"]
    intervals = [row for row in count_cases if row["number"] in saved["applied_cases"]]
    assert len(intervals) == 10 and set(saved["applied_cases"]) <= set(count_audit["completed_cases"])
    exclusions = [row for row in md["patterns"] if row["mode"] == "exclusion"]
    assert len(exclusions) == 3

    # Normalize both orientations of every original row directly. This does not
    # reuse the builder's joint-min canonical keys or its quotient/remainder slices.
    reference = collections.defaultdict(set)
    for word, bounds in ref235:
        assert all((lo == hi and 1 <= lo < 6) or (lo == 6 and hi == 21) for lo, hi in bounds)
    raw_reference = [(w, tuple(lo for lo, hi in bs)) for w, bs in ref235]
    raw_reference += [(w, tuple(c)) for w, c in ref236]
    joint_keys = set()
    for word, counts in raw_reference:
        assert len(word) == len(counts) + 1 and 2 <= len(counts) <= 6
        orientations = [(canonical(word), tuple(counts)), (canonical(word[::-1]), tuple(counts[::-1]))]
        joint_keys.add(min(orientations))
        for w, c in orientations:
            reference[w].add(c)
    assert len(joint_keys) == 1378
    assert sum(len(v) for v in reference.values()) == 2678
    reference_tables = {}
    for w, vectors in reference.items():
        width = len(w) - 1
        table = np.zeros(6 ** width, dtype=bool)
        table[[encode(c) for c in vectors]] = True
        reference_tables[w] = table

    # Reverse rules and their tested positions instead of reversing the candidate.
    oriented_short = []
    for row in short:
        word = row["dirs"]
        length = len(word)
        positions = row.get("positions", [row.get("position")])
        if not row["source"].startswith("47") and row["kind"] != "sum":
            assert all(cap < 6 for cap in row["caps"])
        oriented_short.append((canonical(word), positions, row))
        oriented_short.append((canonical(word[::-1]), [length - j for j in positions], row))
    oriented_intervals = []
    for row in intervals:
        bounds = [tuple(x) for x in row["bounds"]]
        assert len(row["dirs"]) == 5 and len(bounds) == 4
        assert all(lo <= 6 and (hi < 6 or hi == 21) for lo, hi in bounds)
        oriented_intervals += [(canonical(row["dirs"]), bounds), (canonical(row["dirs"][::-1]), bounds[::-1])]

    words = sm["extensions"]
    histories = [tuple(p) for p in md["prefixes"]]
    shapes = {tuple(w): i for i, w in enumerate(sm["direction_shapes"])}
    D, H, K = len(words), len(histories), 6 ** 6
    assert (D, H, K) == (505, 75, 46656)
    graph_relative = "milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz"
    graph_path = ROOT / graph_relative
    PINS[graph_relative] = digest_file(graph_path)
    with np.load(graph_path) as archive:
        direction = archive["direction"]
        history = archive["history"]
        assert hashlib.sha256(memoryview(direction)).hexdigest() == saved["arrays_sha256"]["direction"]
        assert hashlib.sha256(memoryview(history)).hexdigest() == saved["arrays_sha256"]["history"]
        assert np.all((direction >= 0) & (direction < D))
        assert np.all((history >= 0) & (history < H))
        blocks = H * direction + history
        del direction, history
        assert np.all(blocks[1:] >= blocks[:-1])
        block_counts = np.bincount(blocks, minlength=D * H)
        offsets = np.concatenate(([0], np.cumsum(block_counts)))
        del blocks
        actual_codes = archive["count_code"]
        assert hashlib.sha256(memoryview(actual_codes)).hexdigest() == saved["arrays_sha256"]["count_code"]
    codes = np.arange(K, dtype=np.int32)
    digits = np.stack([(codes // 6 ** power) % 6 + 1 for power in range(5, -1, -1)], axis=1).astype(np.int16)
    bucket_upper = np.where(digits == 6, 21, digits)
    failures = []
    compatible_count = incompatible_count = compared_edges = 0
    reference_placements = short_placements = interval_placements = history_placements = 0
    computed_counts = np.zeros(D * H, dtype=np.int64)
    for di, word in enumerate(words):
        retain = np.ones(K, dtype=bool)
        # Reference matching: explicit digit slice encoded left to right.
        for width in range(2, 7):
            for start in range(7 - width):
                piece = canonical(word[start + 2:start + width + 3])
                table = reference_tables.get(piece)
                if table is None:
                    continue
                reference_placements += len(reference[piece])
                slice_code = np.zeros(K, dtype=np.int32)
                for column in range(start, start + width):
                    slice_code = 6 * slice_code + digits[:, column] - 1
                retain &= ~table[slice_code]
        for rule_word, positions, row in oriented_short:
            length = len(rule_word)
            for start in range(10 - length):
                if canonical(word[start:start + length]) != rule_word:
                    continue
                absolute = [start + j for j in positions]
                if any(j < 3 or j > 8 for j in absolute):
                    continue
                short_placements += 1
                vals = digits[:, [j - 3 for j in absolute]]
                if row["source"].startswith("47"):
                    reject = vals[:, 0] == 1
                elif row["kind"] == "sum":
                    reject = (vals.sum(axis=1) <= row["cap"]) & (vals.max(axis=1) < 6)
                else:
                    reject = np.all(vals <= np.asarray(row["caps"]), axis=1)
                retain &= ~reject
        for rule_word, bounds in oriented_intervals:
            for start in [2, 3, 4]:
                if canonical(word[start:start + 5]) != rule_word:
                    continue
                interval_placements += 1
                # Full bucket containment: symbol six denotes [6,21].
                reject = np.ones(K, dtype=bool)
                for j, (lo, hi) in enumerate(bounds):
                    column = start - 2 + j
                    reject &= (digits[:, column] >= lo) & (bucket_upper[:, column] <= hi)
                retain &= ~reject
        ps = shapes[canonical(word[:8])]
        for q, prefix in enumerate(histories):
            block = H * di + q
            left, right = int(offsets[block]), int(offsets[block + 1])
            actual = actual_codes[left:right]
            if q and md["compatible_shapes"][q] != ps:
                incompatible_count += 1
                if len(actual):
                    failures.append(dict(direction=di, history=q, reason="incompatible block nonempty", actual_count=len(actual)))
                continue
            compatible_count += 1
            accepted = retain.copy()
            full_history = prefix + (di,)
            for row in exclusions:
                if len(full_history) < 3 or full_history[-3:] != tuple(row["signature"]):
                    continue
                history_placements += 1
                reject = np.ones(K, dtype=bool)
                for position, cap in row["caps"].items():
                    reject &= digits[:, int(position)] <= cap
                accepted &= ~reject
            expected = codes[accepted]
            computed_counts[block] = len(expected)
            compared_edges += len(expected)
            if not np.array_equal(expected, actual):
                failures.append(dict(direction=di, history=q, expected_count=len(expected), actual_count=len(actual), missing_codes=np.setdiff1d(expected, actual)[:32].tolist(), extra_codes=np.setdiff1d(actual, expected)[:32].tolist(), reason="ordered accepted list differs"))
    REPORT.update(
        status="PASS_EXACT_RETAINED_CODE_LISTS" if not failures else "FAIL_RETAINED_CODE_LISTS",
        all_block_positions=D * H,
        compatible_blocks_compared=compatible_count,
        incompatible_blocks_verified_empty=incompatible_count,
        direction_code_pairs=D * K,
        compatible_candidate_keys=compatible_count * K,
        saved_edges=len(actual_codes),
        independently_retained_edges=compared_edges,
        differing_blocks=len(failures),
        differences=failures,
        counts_equal=bool(np.array_equal(computed_counts, block_counts)),
        per_block_counts_sha256=hashlib.sha256(computed_counts.astype("<i8").tobytes()).hexdigest(),
        logical_reference_placements=reference_placements,
        oriented_short_placements=short_placements,
        oriented_interval_placements=interval_placements,
        active_history_placements=history_placements,
        interval_case_numbers=saved["applied_cases"],
        independent_choices=["reference union expands both original orientations before deduplication", "count slices encoded from explicit digit columns", "short rules and their positions reversed rather than candidate words", "interval rules reversed with their bounds", "full count-bucket containment used for intervals", "reference, short and interval masks factored by direction; history masks applied per compatible block"],
        endpoints="Already independently checked for all rows in data/array-order-audit.json; not rechecked in this run.",
    )
    assert compatible_count == 791 and incompatible_count == 37084
    assert not failures and REPORT["counts_equal"]
    assert compared_edges == len(actual_codes) == 4947008


if __name__ == "__main__":
    try:
        main()
        # Detect an input modified during the check before reporting success.
        for relative, before in PINS.items():
            assert digest_file(ROOT / relative) == before, f"Input changed during audit: {relative}"
    except BaseException as exc:
        REPORT["status"] = "FAIL_RETAINED_CODE_LISTS"
        REPORT["error"] = repr(exc)
        raise
    finally:
        REPORT["input_sha256"] = PINS
        REPORT["script_sha256"] = digest_file(Path(__file__))
        REPORT["seconds"] = time.monotonic() - START
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(REPORT, indent=2) + "\n", encoding="utf-8")
        print({k: v for k, v in REPORT.items() if k not in {"input_sha256", "independent_choices", "differences"}}, flush=True)
