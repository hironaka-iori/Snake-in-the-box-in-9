"""Reproduce the saved-array ordering, rank, endpoints and multiplicity audit.
Read-only inputs. Prior output receipts are preserved by hash before replacement.
No solver, historical graph builder, or Lean process is run.
"""
from pathlib import Path
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "work/solver_packages"))
import numpy as np

OUT = HERE / "data/array-order-audit.json"
START = time.monotonic()
PINS = {}
REPORT = {"status": "RUNNING"}


def filehash(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def pin(relative):
    result = filehash(ROOT / relative)
    PINS[relative] = result
    return result


def read(relative):
    raw = (ROOT / relative).read_bytes()
    PINS[relative] = hashlib.sha256(raw).hexdigest()
    return json.loads(raw.decode("utf-8-sig"))


def canon(word):
    labels = list(dict.fromkeys(word))
    return tuple(labels.index(x) for x in word)


def main():
    sm = read("milestones/59-extended-share-window/extended/data/model.json")
    md = read("milestones/67-critical-family-charge/data/full-model.json")
    meta = read("milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json")
    e70 = read("milestones/70-proof-supported-share-model/data/enriched-model.json")
    m72 = read("milestones/72-four-count-proof-closure/data/proved-model.json")
    m73 = read("milestones/73-countfree-share-catalogue/data/proved-model.json")
    for field in ["prefixes", "patterns", "compatible_shapes"]:
        assert e70[field] == md[field]
    prefixes = [tuple(p) for p in md["prefixes"]]
    H, D, B, K, N, S = len(prefixes), len(sm["extensions"]), 6 ** 5, 6 ** 6, sm["states"], md["states"]
    assert (D, H, B, K, N, S) == (505, 75, 7776, 46656, 1026432, 1601856)
    assert prefixes[0] == () and len(set(prefixes)) == H
    sid = {tuple(w): i for i, w in enumerate(sm["direction_shapes"])}
    assert len(sid) == 132
    valid = np.zeros(D * H, dtype=bool)
    nextq = np.full(D * H, -1, dtype=np.int32)
    sourcebase = np.full(D * H, -1, dtype=np.int32)
    targetbase = np.full(D * H, -1, dtype=np.int32)
    source_shape, target_shape, history_hits = [], [], []
    for di, word in enumerate(sm["extensions"]):
        ps, ts = sid[canon(word[:8])], sid[canon(word[1:])]
        source_shape.append(ps)
        target_shape.append(ts)
        for q, prefix in enumerate(prefixes):
            block = H * di + q
            if q and md["compatible_shapes"][q] != ps:
                continue
            valid[block] = True
            history = prefix + (di,)
            choices = [j for j, p in enumerate(prefixes) if p and len(p) <= len(history) and history[-len(p):] == p]
            nq = max(choices, key=lambda j: len(prefixes[j])) if choices else 0
            assert not nq or md["compatible_shapes"][nq] == ts
            nextq[block] = nq
            sourcebase[block] = ps * B if q == 0 else N + (q - 1) * B
            targetbase[block] = ts * B if nq == 0 else N + (nq - 1) * B
            for pattern in md["patterns"]:
                if pattern["mode"] == "exclusion" and len(history) >= 3 and history[-3:] == tuple(pattern["signature"]):
                    history_hits.append(dict(direction=di, history=q, signature=pattern["signature"], caps=pattern["caps"]))

    hashes, stages = {}, {}
    stage_inputs = [
        ("enriched70", "milestones/70-proof-supported-share-model/build/enriched-graph.npz", e70),
        ("proved72", "milestones/72-four-count-proof-closure/build/proved-graph.npz", m72),
        ("source_current", "milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz", meta),
    ]
    for title, relative, metadata in stage_inputs:
        archive_hash = pin(relative)
        raw_hashes, details = {}, {}
        with np.load(ROOT / relative) as archive:
            assert set(archive.files) == {"U", "V", "weight", "direction", "count_code", "history"}
            for name in archive.files:
                values = archive[name]
                assert values.shape == (metadata["edges"],) and values.dtype == np.dtype("<i4")
                raw_hashes[name] = hashlib.sha256(memoryview(values)).hexdigest()
                assert raw_hashes[name] == metadata["arrays_sha256"][name]
                details[name] = dict(length=len(values), dtype=str(values.dtype), minimum=int(values.min()), maximum=int(values.max()))
                del values
        hashes[title] = raw_hashes
        stages[title] = dict(path=relative, file_sha256=archive_hash, file_bytes=(ROOT / relative).stat().st_size, arrays=details)
    for name in ["U", "V", "direction", "count_code", "history"]:
        assert hashes["proved72"][name] == hashes["source_current"][name]
        assert m73["source_arrays_sha256"][name] == hashes["source_current"][name]
    assert m72["source_arrays_sha256"] == hashes["enriched70"]
    assert meta["source_arrays_sha256"] == hashes["proved72"]
    assert m73["source_arrays_sha256"] == hashes["source_current"]

    with np.load(ROOT / stage_inputs[-1][1]) as archive:
        direction, history = archive["direction"], archive["history"]
        assert np.all((0 <= direction) & (direction < D))
        assert np.all((0 <= history) & (history < H))
        blocks = direction * H + history
        del direction, history
        assert np.all(blocks[1:] >= blocks[:-1])
        counts = np.bincount(blocks, minlength=D * H).astype(np.int64)
        offsets = np.concatenate((np.array([0], dtype=np.int64), np.cumsum(counts)))
        assert int(offsets[-1]) == meta["edges"] and np.all(counts[~valid] == 0)
        codes = archive["count_code"]
        assert np.all((0 <= codes) & (codes < K))
        bad_order = duplicates = 0
        for lo in range(1, len(codes), 262144):
            hi = min(len(codes), lo + 262144)
            same = blocks[lo:hi] == blocks[lo-1:hi-1]
            bad_order += int(np.count_nonzero(same & (codes[lo:hi] <= codes[lo-1:hi-1])))
            duplicates += int(np.count_nonzero(same & (codes[lo:hi] == codes[lo-1:hi-1])))
        assert bad_order == duplicates == 0
        del blocks
        rank_errors = 0
        first_codes, last_codes = [], []
        for block in range(D * H):
            lo, hi = int(offsets[block]), int(offsets[block + 1])
            part = codes[lo:hi]
            if len(part):
                rank_errors += int(np.count_nonzero(np.searchsorted(part, part) != np.arange(len(part))))
                first_codes.append(int(part[0]))
                last_codes.append(int(part[-1]))
            else:
                first_codes.append(None)
                last_codes.append(None)
        assert rank_errors == 0
        formula_checks = {}
        for name, bases, op in [("U", sourcebase, "div6"), ("V", targetbase, "mod7776")]:
            values = archive[name]
            errors = 0
            for block in range(D * H):
                lo, hi = int(offsets[block]), int(offsets[block + 1])
                if hi == lo:
                    continue
                expected = int(bases[block]) + (codes[lo:hi] // 6 if op == "div6" else codes[lo:hi] % B)
                errors += int(np.count_nonzero(values[lo:hi] != expected))
            assert errors == 0
            formula_checks[name] = dict(edges_checked=len(values), mismatches=errors)
            del values
        del codes, part
        packed = archive["U"].astype(np.int64)
        packed *= S
        target = archive["V"]
        packed += target
        del target
        packed.sort()
        same_pair = packed[1:] == packed[:-1]
        duplicate_pairs = int(same_pair.sum())
        breaks = np.flatnonzero(~same_pair) + 1
        runs = np.diff(np.concatenate(([0], breaks, [len(packed)])))
        multiplicity = dict(unique_pairs=int(len(packed)-duplicate_pairs), duplicate_rows_beyond_first=duplicate_pairs, repeated_endpoint_pairs=int(np.count_nonzero(runs > 1)), maximum_multiplicity=int(runs.max()), scope="Distinct ordered candidate keys may have the same U,V. This is a directed multigraph; key uniqueness does not imply endpoint-pair uniqueness.")
        del packed, same_pair, breaks, runs

    ref = read("milestones/54-share-coverage/data/keys_235.json")["keys"]
    older = read("milestones/39-audited-bound-236/data/exclusion-catalogue.json")
    assert all(all((lo == hi and 1 <= lo < 6) or (lo == 6 and hi == 21) for lo, hi in bs) for w, bs in ref)
    keys = {min((canon(w), tuple(c)), (canon(w[::-1]), tuple(c[::-1]))) for w, c in [(w, [lo for lo, hi in bs]) for w, bs in ref] + older}
    assert len(keys) == 1378
    rows = []
    for prior in ["47-critical-singleton-patterns", "48-low-count-compatibility", "49-six-direction-pair-catalogue"]:
        rows += [dict(row, source=prior) for row in read(f"milestones/{prior}/data/cases.json")]
    rows.append(dict(number=501, source="50-three-count-return", dirs=[0,1,2,3,4,0], positions=[1,4,5], kind="sum", cap=12))
    assert rows == e70["additional_proved_rules"] and len(rows) == 40
    sums = [row for row in rows if row.get("kind") == "sum"]
    assert len(sums) == 3
    cases = read("milestones/72-four-count-proof-closure/data/cases.json")
    applied = [row for row in cases if row["number"] in meta["applied_cases"]]
    assert len(applied) == 10
    assert set(meta["applied_cases"]) <= set(read("milestones/72-four-count-proof-closure/data/proof-audit.json")["completed_cases"])
    for relative in [
        "milestones/70-proof-supported-share-model/scripts/build.py",
        "milestones/72-four-count-proof-closure/scripts/graph.py",
        "milestones/72-four-count-proof-closure/scripts/verify_graph.py",
        "milestones/72-four-count-proof-closure/critical-current/scripts/prepare.py",
    ]:
        pin(relative)
    REPORT.update(
        status="PASS_SOURCE_DERIVED_ARRAY_ORDER_AND_ENDPOINTS",
        scope="Direct source-derived formulas and sequential NumPy array audit. No historical builder or solver replay. Exact predicate equality is a separate computational check in retention-equality.json; neither receipt establishes Lean finite-array equality.",
        ordering=["direction", "history", "count_code"], direction_count=D, history_count=H,
        all_block_positions=D*H, compatible_blocks=int(valid.sum()), nonempty_blocks=int(np.count_nonzero(counts)),
        compatible_empty_blocks=int(np.count_nonzero(valid & (counts == 0))), incompatible_blocks=int(np.count_nonzero(~valid)),
        edges=meta["edges"], block_count_min=int(counts[valid].min()), block_count_max=int(counts.max()),
        count_code_range=[0,K-1], strict_lexicographic_order=True, duplicate_keys=duplicates, rank_mismatches=rank_errors,
        endpoint_formula_checks=formula_checks, history_target_compatibility_errors=[], history_exclusion_active_blocks=history_hits,
        reference_key_count=len(keys), short_rule_count=len(rows),
        sum_rules=[dict(number=row["number"], source=row["source"], dirs=row["dirs"], positions=row["positions"], cap=row["cap"]) for row in sums],
        interval_case_numbers=meta["applied_cases"],
        retention_rule_families=["source history/direction compatibility", "reference union, widths 2..6, both orientations at all fitting offsets", "40 enriched short rules, with unsaturated guards for sums", "three emitted-signature count-cap exclusions", "ten proved-only four-count interval exclusions"],
        stages=stages, array_sha256=hashes, block_index="75*direction + history", block_counts=counts.tolist(), block_offsets=offsets.tolist(),
        compatible_block_ids=np.flatnonzero(valid).tolist(), nonempty_block_ids=np.flatnonzero(counts).tolist(),
        block_first_codes=first_codes, block_last_codes=last_codes, source_shapes=source_shape, target_shapes=target_shape,
        block_next_history=nextq.tolist(), constants=dict(B=B, N=N, states=S),
        rank_index="block_offsets[75*d+q] + number of saved accepted codes strictly smaller than c in that block",
        current_short_catalogues_equal_saved_rows=True, endpoint_pair_multiplicity=multiplicity,
        per_block_counts_sha256=hashlib.sha256(counts.astype("<i8").tobytes()).hexdigest(),
    )
    for relative, before in PINS.items():
        assert filehash(ROOT / relative) == before, f"Input changed during audit: {relative}"


if __name__ == "__main__":
    try:
        main()
    except BaseException as exc:
        REPORT["status"] = "FAIL_ARRAY_ORDER_OR_ENDPOINTS"
        REPORT["error"] = repr(exc)
        raise
    finally:
        REPORT["file_sha256"] = PINS
        REPORT["script_sha256"] = filehash(Path(__file__))
        REPORT["seconds"] = time.monotonic() - START
        OUT.parent.mkdir(parents=True, exist_ok=True)
        if OUT.exists():
            previous = OUT.read_bytes()
            previous_sha = hashlib.sha256(previous).hexdigest()
            backup = OUT.with_name(f"array-order-audit.previous-{previous_sha[:16]}.json")
            if backup.exists():
                assert backup.read_bytes() == previous, "Refusing to overwrite a different archived receipt"
            else:
                backup.write_bytes(previous)
            REPORT["previous_receipt"] = dict(path=backup.relative_to(ROOT).as_posix(), sha256=previous_sha)
        OUT.write_text(json.dumps(REPORT, indent=2) + "\n", encoding="utf-8")
        omitted = {"file_sha256", "stages", "array_sha256", "block_counts", "block_offsets", "compatible_block_ids", "nonempty_block_ids", "block_first_codes", "block_last_codes", "source_shapes", "target_shapes", "block_next_history"}
        print({k:v for k,v in REPORT.items() if k not in omitted}, flush=True)
