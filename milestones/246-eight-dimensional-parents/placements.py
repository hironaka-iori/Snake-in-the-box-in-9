"""Enumerate rooted Q8 placements and verify every reported minimum's representative."""
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from guarded import memory_limit, wait_for_gate


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def shape(path):
    def normalized(seq):
        names = {}
        return tuple(names.setdefault(i, len(names)) for i in seq)
    transitions = [(a ^ b).bit_length() - 1 for a, b in zip(path, path[1:])]
    return min(normalized(transitions), normalized(reversed(transitions)))


def rooted(path, endpoint):
    ordered = path if endpoint == 0 else path[::-1]
    return [x ^ ordered[0] for x in ordered]


def permute(x, image):
    return sum(1 << image[i] for i in range(8) if x & (1 << i))


def verify(path, dimension):
    if len(path) != len(set(path)) or any(v < 0 or v >= (1 << dimension) for v in path):
        raise ValueError("Repeated vertex or out-of-range vertex")
    for (i, u), (j, v) in combinations(enumerate(path), 2):
        if ((u ^ v).bit_count() == 1) != (j == i + 1):
            raise ValueError(("Unverified induced path", i, j))
    return len(path) * (len(path) - 1) // 2


def main():
    limit = memory_limit(256)
    donors_file = HERE / "donors.json"
    comp_file = HERE / "comparison.json"
    donors = json.loads(donors_file.read_bytes())["shapes"]
    comp = json.loads(comp_file.read_bytes())
    paths = [entry["path"] for entry in donors]
    lengths = [len(path) - 1 for path in paths]
    inventory = Counter(lengths)
    assert inventory == {93: 364, 94: 375, 95: 149, 96: 11, 97: 3, 98: 1}
    shapes = {shape(path): i for i, path in enumerate(paths)}
    assert len(shapes) == len(paths)
    for path in paths:
        verify(path, 8)
    tasks = []
    for long_length, short_length in ((98, 93), (97, 94), (96, 95)):
        tasks.extend((a, b, "target_192") for a, b in product(
            [i for i, n in enumerate(lengths) if n == long_length],
            [i for i, n in enumerate(lengths) if n == short_length]))
    controls = {}
    for row in comp["one_crossing_pairs"]:
        key = (shapes[shape(row["long"])], shapes[shape(row["short"])])
        assert key not in controls
        controls[key] = row["seed"]
    assert len(controls) == 25 and len(tasks) == 3128
    tasks.extend((a, b, "control_191") for a, b in controls)
    tasks.sort()
    compiler = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
    source = HERE / "Place.cs"
    with TemporaryDirectory(prefix="snake246-placements-") as temp:
        folder = Path(temp)
        exe = folder / "Place.exe"
        input_file = folder / "paths.txt"
        output_file = folder / "minima.txt"
        with input_file.open("w", encoding="ascii") as f:
            print(len(paths), file=f)
            for path in paths:
                print(*path, file=f)
            print(len(tasks), file=f)
            for a, b, _ in tasks:
                print(a, b, file=f)
        compile_record = wait_for_gate(
            [str(compiler), "/nologo", "/optimize+", "/platform:x64", "/out:" + str(exe), str(source)],
            folder, HERE / "placements-compile.log", 90)
        run_record = wait_for_gate([str(exe), str(input_file), str(output_file)],
                                   folder, HERE / "placements-survey.log", 600)
        raw = output_file.read_text("ascii").splitlines()
        assert len(raw) == len(tasks)
        executable_hash = digest(exe)
        data_hash = digest(output_file)

    records = []
    histogram = {}
    for line, (expected_a, expected_b, scope) in zip(raw, tasks):
        parts = line.split()
        a, b, minimum, hits, end_a, end_b = map(int, parts[:6])
        image = list(map(int, parts[6]))
        assert (a, b) == (expected_a, expected_b) and sorted(image) == list(range(8))
        assert 1 <= hits <= 161280 and end_a in (0, 1) and end_b in (0, 1)
        first = [permute(x, image) for x in rooted(paths[a], end_a)]
        second = rooted(paths[b], end_b)
        assert set(first).intersection(second) - {0} == set(first[1:]).intersection(second[1:])
        assert len(set(first[1:]).intersection(second[1:])) == minimum
        row = dict(long_donor=a, short_donor=b, lengths=[lengths[a], lengths[b]], scope=scope,
                   min_extra_overlap=minimum, minimizing_placements=hits,
                   long_endpoint=end_a, short_endpoint=end_b, axis_image=image)
        if scope == "control_191":
            assert minimum == 0
            row["bank_example"] = controls[a, b]
        if minimum == 0:
            witness = first[::-1] + [256 + v for v in second]
            row["witness"] = witness
            row["q9_pairs_checked"] = verify(witness, 9)
            assert len(witness) - 1 == (192 if scope == "target_192" else 191)
        family = str(lengths[a]) + "+" + str(lengths[b])
        histogram.setdefault(family, Counter())[minimum] += 1
        records.append(row)

    result = dict(input_hashes={p.name: digest(p) for p in (donors_file, comp_file, source, Path(__file__))},
                  donor_ids="Zero-based indices into donors.json shapes.",
                  placement="Translate each chosen endpoint to zero, permute the longer arm axes by axis_image. Endpoint 0 is first, 1 last.",
                  placements_per_pair=161280, target_pairs=3128, positive_control_pairs=25,
                  target_placements=3128 * 161280, positive_control_placements=25 * 161280,
                  minimum_histogram=histogram, records=records)
    result_file = HERE / "placements.json"
    result_file.write_text(json.dumps(result, separators=(",", ":")) + "\n", encoding="utf-8")
    receipt = dict(status="pass", compiler=str(compiler), compiler_sha256=digest(compiler),
                   executable_sha256=executable_hash, private_limit=limit, compile=compile_record,
                   survey=run_record, raw_output_sha256=data_hash, result_sha256=digest(result_file))
    (HERE / "placements-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print("Minimum extra overlap histograms by length pair:", histogram)


if __name__ == "__main__":
    main()
