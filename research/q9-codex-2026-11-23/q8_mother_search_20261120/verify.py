"""Verify the witnesses, recount placements, and optionally rerun the native searches."""
import argparse
import collections
import csv
import hashlib
import itertools
import json
import math
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
STAGES = ("segment", "regrow", "level96", "level95", "level94")
EXPECTED = (84, 91, 82, 90, 103)

def norm(word):
    labels = {}
    return "".join(str(labels.setdefault(d, len(labels))) for d in word)

def canonical(word):
    return min(norm(word), norm(word[::-1]))

def vertices(word):
    result = [0]
    for digit in word:
        assert digit in "01234567"
        result.append(result[-1] ^ (1 << int(digit)))
    return result

def valid(path, dimension):
    return (all(0 <= v < 1 << dimension for v in path)
            and len(set(path)) == len(path)
            and all(((u ^ v).bit_count() == 1) == (j == i + 1)
                    for i, u in enumerate(path) for j, v in enumerate(path) if i < j))

def rooted_subwords(word):
    result = set()
    for size in range(93, len(word) + 1):
        for start in range(len(word) - size + 1):
            part = word[start:start + size]
            result.update((norm(part), norm(part[::-1])))
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay-joins", action="store_true")
    parser.add_argument("--regenerate", action="store_true")
    parser.add_argument("--compiler", default="clang++")
    opt = parser.parse_args()
    base = EVIDENCE / "baseline.txt"
    digest = hashlib.sha256(base.read_bytes()).hexdigest()
    assert digest == json.loads((EVIDENCE / "baseline_manifest.json").read_text())["bank_sha256"]
    baseline = set(base.read_text().split())
    previous = set(baseline)
    positive = json.loads((EVIDENCE / "control_191.json").read_text())
    p = positive["vertices"]
    assert valid(p, 9) and len(p) == 192
    assert not valid([0, 1, 3, 2], 8) and not valid([0, 1, 0], 8)
    assert not valid([0, 3], 8)
    historical = json.loads((EVIDENCE / "previous_97.json").read_text())["record"]["vertices"]
    assert valid(historical, 8) and len(historical) == 98
    history = "".join(str((x ^ y).bit_length() - 1) for x, y in zip(historical, historical[1:]))
    historical_words = {canonical(history), canonical(history[:-1]), canonical(history[1:])}
    rows = list(csv.DictReader((ROOT / "mothers.tsv").open(), delimiter="\t"))
    assertions = {r["canonical_transition_word"]: r for r in rows}
    assert len(assertions) == len(rows) == 451
    seen = set()
    total = collections.Counter()
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        if opt.replay_joins:
            subprocess.run([opt.compiler, "-O3", "-std=c++17", str(ROOT / "src/join.cpp"), "-o", str(tmp / "join")], check=True)
        for stage, count in zip(STAGES, EXPECTED):
            raw = (EVIDENCE / (stage + ".raw")).read_text()
            fresh = set()
            size_counts = collections.Counter()
            for line in raw.splitlines():
                word = line.split()[0]
                code = canonical(word)
                assert code not in baseline and code not in seen
                assert valid(vertices(word), 8) and assertions[code]["stage"] == stage
                assert int(assertions[code]["edges"]) == len(code)
                expected_history = ("previous_97" if len(code) == 97 else "trim_of_previous_97") if code in historical_words else "not_matched_in_audited_q8_files"
                assert assertions[code]["history"] == expected_history
                seen.add(code)
                size_counts[len(word)] += 1
                fresh.update(rooted_subwords(word))
            assert size_counts[96] == count and size_counts[97] == (stage == "level96")
            fresh -= previous
            expected_log = (EVIDENCE / (stage + ".log")).read_text()
            fc = collections.Counter(map(len, fresh))
            ac = collections.Counter(map(len, previous | fresh))
            for line in expected_log.splitlines():
                goal, tag, cases, hits, zero = line.split()
                assert tag == "ordered_rooted_placements" and hits == "hits" and zero == "0"
                expected = math.factorial(8) * sum(count * ac[int(goal) - k - 1] for k, count in fc.items())
                assert int(cases) == expected
                total[int(goal)] += expected
            fresh_file = tmp / "fresh"
            fresh_file.write_text("".join(w + "\n" for w in sorted(fresh)))
            if opt.replay_joins:
                inp = "".join(w + "\n" for w in sorted(previous))
                result = subprocess.run([tmp / "join", fresh_file], input=inp, text=True, capture_output=True, check=True)
                assert result.stdout == expected_log, stage
            if opt.regenerate:
                executable = tmp / stage
                subprocess.run([opt.compiler, "-O3", "-std=c++17", str(ROOT / "src" / (stage + ".cpp")), "-o", executable], check=True)
                extra = tmp / "parents"
                extra.write_text("".join(w + "\n" for w in sorted(previous - baseline)))
                args = {"segment": ["15000", "9000"], "regrow": [extra, "15000", "15000"],
                        "level96": [extra, "40000"], "level95": [extra, "65000"], "level94": [extra, "75000"]}[stage]
                result = subprocess.run([executable, *args], input=base.read_text(), text=True, capture_output=True, check=True)
                assert {canonical(line.split()[0]) for line in result.stdout.splitlines()} == {canonical(line.split()[0]) for line in raw.splitlines()}, stage
            previous.update(fresh)
    assert seen == set(assertions)
    print(json.dumps(dict(checked_classes=dict(collections.Counter(map(len, seen))),
                          historical_matches=len(seen & historical_words),
                          fresh_rooted_by_edges=dict(collections.Counter(map(len, previous - baseline))),
                          placements=total, total_placements=sum(total.values()), positive_control_edges=191,
                          negative_controls=3, replayed_joins=opt.replay_joins, regenerated=opt.regenerate),indent=2))
if __name__ == "__main__":
    main()
