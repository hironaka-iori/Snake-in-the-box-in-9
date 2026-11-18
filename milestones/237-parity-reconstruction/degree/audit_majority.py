"""Independently reconstruct every archived row from the saved seed and Hamming distance."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASES = ROOT / "milestones/236-parity-exchange-frontier/data/bases.json"
LOW = -(1 << 63)
NEIGHBOURS = [[w for w in range(512) if (v ^ w).bit_count() == 1] for v in range(512)]


def row(terms, bounds, guard=None):
    return (tuple(sorted(terms)), tuple(bounds), guard)


def expected(seed, cycles):
    parity = seed[0].bit_count() % 2
    majority = {v for v in range(512) if v.bit_count() % 2 == parity}
    minority = set(range(512)) - majority
    rows = Counter()
    for group, total, prefix in [(seed, 95, "v"), (majority, 97, "v"), (minority, 96, "v"), (majority, 2, "e")]:
        rows[row([(f"{prefix}{v}", 1) for v in group], [total, total])] += 1
    for v in majority:
        rows[row([(f"e{v}", 1), (f"v{v}", -1)], [LOW, 0])] += 1
    for v in range(512):
        terms = [(f"v{w}", 1) for w in NEIGHBOURS[v]]
        if v in majority:
            terms.append((f"e{v}", 1))
        rows[row(terms, [2, 2], f"v{v}")] += 1
    for cycle in cycles:
        assert len(cycle) == len(set(cycle)) >= 4
        assert all(len(set(NEIGHBOURS[v]).intersection(cycle)) == 2 for v in cycle)
        rows[row([(f"v{v}", 1) for v in cycle], [LOW, len(cycle) - 1])] += 1
    return rows, majority


def inspect(content, seed, cycles):
    text = content.decode()
    variables, *constraints = text.strip().split("constraints {")
    pattern = r'variables\s*\{\s*name: "([ve]\d+)"\s*domain: 0\s*domain: 1\s*\}'
    names = re.findall(pattern, variables)
    assert not re.sub(pattern, "", variables).strip()
    wanted, majority = expected(seed, cycles)
    assert len(names) == 768 and set(names) == ({f"v{v}" for v in range(512)} | {f"e{v}" for v in majority})
    actual = Counter()
    for constraint in constraints:
        head = re.fullmatch(r"\s*(?:enforcement_literal: (\d+)\s*)?linear \{([^{}]*)\}\s*\}\s*", constraint)
        assert head
        guard = None if head[1] is None else names[int(head[1])]
        pattern = r"(vars|coeffs|domain): (-?\d+)"
        assert not re.sub(pattern, "", head[2]).strip()
        fields = {"vars": [], "coeffs": [], "domain": []}
        for field, value in re.findall(pattern, head[2]):
            fields[field].append(int(value))
        assert len(fields["vars"]) == len(fields["coeffs"])
        actual[row([(names[i], c) for i, c in zip(fields["vars"], fields["coeffs"])], fields["domain"], guard)] += 1
    assert actual == wanted


def main(labels):
    bases = json.loads(BASES.read_bytes())["bases"]
    statuses = {}
    count = 0
    archives = {}
    for label in labels:
        result = json.loads((HERE / (label + ".json")).read_bytes())
        assert result["base_sha256"] == sha256(BASES.read_bytes()).hexdigest()
        assert result["script_sha256"] == sha256((HERE / "majority_survey.py").read_bytes()).hexdigest()
        path = HERE / (label + "-models.zip")
        archives[label] = sha256(path.read_bytes()).hexdigest()
        requested = result["arguments"]["bases"]
        assert [r["base"] for r in result["results"]] == (list(range(145)) if requested is None else requested)
        with ZipFile(path) as archive:
            for record in result["results"]:
                cycles = []
                for index, iteration in enumerate(record["iterations"]):
                    name = f'base{record["base"]:03d}-iteration{index}.pbtxt'
                    assert iteration["model"] == name
                    content = archive.read(name)
                    assert sha256(content).hexdigest() == iteration["sha256"]
                    inspect(content, bases[record["base"]]["vertices"], cycles)
                    cycles.extend(iteration.get("cycles", []))
                    count += 1
                assert record["status"] == record["iterations"][-1]["status"] == "INFEASIBLE" or record["status"] in ("UNKNOWN", "WITNESS")
                statuses[record["base"]] = record["status"]
    assert set(statuses) == set(range(145))
    summary = dict(models=count, classes=len(statuses), outcomes=dict(Counter(statuses.values())), archives=archives,
                   scope="Exact model rows and hashes inspected. INFEASIBLE is the recorded CP-SAT outcome; no Lean contradiction replay.")
    (HERE / "audit.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary))


if __name__ == "__main__":
    main(sys.argv[1:])
