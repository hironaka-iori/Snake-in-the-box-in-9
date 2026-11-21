"""Search unrestricted rooted partners for the specified 96-edge arms and replay their proofs."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic

HERE = Path(__file__).resolve().parent
LAST = HERE.parent / "254-distant-arm-partners"
sys.path.insert(0, str(LAST))
import fixed
from fixed import p, shared, read, require, file_hash, rooted

ARMS = HERE / "arms.json"
LEDGER = HERE / "partner-caps.json"


def sources():
    old, pins, _ = fixed.sources()
    aggregate = read(LAST / "aggregate.json")
    shapes = read(LAST / "parity-families.json")["shapes"]
    require(aggregate["pins"]["parity-families.json"] == file_hash(LAST / "parity-families.json"),
            "Earlier aggregate uses different arms")
    seen = set()
    for row in aggregate["cases"]:
        key, root = row["shape"], row["root"]
        path = shapes[key]
        require(root in (path[0], path[-1]), "Earlier crossing is not an arm endpoint")
        end = int(root == path[-1])
        parent = rooted(path, end)
        cap = row["partner_upper"]
        require(row["parent"] == parent and 0 <= cap < 95 and (key, end) not in seen,
                "Earlier rooted cap differs")
        seen.add((key, end))
        old["254/" + key, end] = (parent, cap)
    require(seen == {(k, end) for k in shapes for end in (0, 1)}, "Earlier coverage differs")
    pins.update({f.name: file_hash(f) for f in (ARMS, Path(__file__), LAST / "aggregate.json",
                                                LAST / "parity-families.json")})
    return old, pins


def select(arms, prefixes, ends):
    ids = arms["outside_previous"]
    require(len(set(ids)) == len(ids) and set(ids) <= arms["shapes"].keys(), "Invalid new-shape list")
    if prefixes:
        ids = []
        for prefix in prefixes:
            matches = [k for k in arms["shapes"] if k.startswith(prefix)]
            require(len(matches) == 1, "Missing or ambiguous shape prefix " + prefix)
            if matches[0] not in ids:
                ids.append(matches[0])
    for key in ids:
        path = arms["shapes"][key]
        p.path_ok(path, 8)
        require(len(path) == 97 and sha256(p.shape(path)).hexdigest() == key, "Invalid 96-edge arm")
        for end in ends:
            yield key, end, path[-1] if end else path[0], rooted(path, end)


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--ids", nargs="+", help="Unique shape prefixes. Default is every new shape.")
    cli.add_argument("--ends", nargs="+", type=int, choices=(0, 1), default=[0, 1])
    cli.add_argument("--length", type=int, default=95, help="Number of edges of the partner")
    cli.add_argument("--seconds", type=float, default=4, help="Search time per query")
    cli.add_argument("--total", type=float, default=150, help="Stop starting queries after this interval")
    cli.add_argument("--depth", type=int, default=0, help="Depth to split open prefixes")
    cli.add_argument("--retry", action="store_true", help="Retry open leaves at the selected depth")
    cli.add_argument("--replay", action="store_true")
    args = cli.parse_args()
    require(1 <= args.length <= 95 and min(args.seconds, args.total) > 0 and 0 <= args.depth <= 8,
            "Unsupported length or limits")
    arms = read(ARMS)
    cases = list(select(arms, args.ids, list(dict.fromkeys(args.ends))))
    old, pins = sources()
    # Earlier modules use HERE for the archive destination, and for their original
    # inputs. Call sources before redirecting either module.
    p.HERE = fixed.HERE = HERE
    data = read(LEDGER) if LEDGER.exists() else dict(pins=pins, roots={})
    require(data["pins"] == pins, "Partner archive inputs differ")
    index = {} if args.replay else p.placement_index(old)
    n = args.length
    report = []
    with TemporaryDirectory(prefix="snake255-partner-") as directory:
        folder = Path(directory)
        checker, trimmer = folder / "VerifyLrat.exe", folder / "TrimLrat.exe"
        compilers = [(p.joins.CHECKER, checker)]
        if not args.replay:
            compilers.append((fixed.R252 / "TrimLrat.cs", trimmer))
        for src, exe in compilers:
            subprocess.run([str(p.joins.COMPILER), "/nologo", "/optimize+", "/out:" + str(exe), str(src)],
                           check=True, capture_output=True, timeout=45)
        deadline = monotonic() + args.total
        for key, end, root, parent in cases:
            tag = key + ":" + str(end)
            entry = data["roots"].get(tag, dict(shape=key, end=end, root=root, parent=parent))
            require((entry["shape"], entry["end"], entry["root"], entry["parent"]) == (key, end, root, parent),
                    "Stored parent differs")
            rows = shared.query_rows(entry, n)
            if args.replay:
                for prefix, row in rows.items():
                    require(prefix == (0,) or prefix[:-1] in rows, "Missing prefix ancestor")
                    shared.check_prefix(parent, n, row)
                    p.model = shared.anchored_model(prefix)
                    p.replay(parent, n, row, old, folder, checker)
            else:
                rules = None
                def visit(prefix):
                    nonlocal rules
                    if monotonic() >= deadline:
                        return
                    row = rows.get(prefix)
                    if row is None or (row["status"] == "open" and args.retry and len(prefix)-1 == args.depth):
                        if rules is None:
                            rules = p.active_cuts(p.transfers(parent, old, index), n)
                        p.model = shared.anchored_model(prefix)
                        seconds = min(args.seconds, max(.01, deadline-monotonic()))
                        answer = p.solve(parent, n, rules, old, folder, checker, seconds, row)
                        fixed.compact(folder, checker, trimmer, answer)
                        row = dict(prefix=list(prefix), **answer)
                        shared.check_prefix(parent, n, row)
                        if row["status"] == "witness":
                            p.verified_partner(parent, row, n)
                        rows[prefix] = row
                        entry[str(n)] = list(rows.values())
                        data["roots"][tag] = entry
                        p.joins.save_json(LEDGER, data)
                        print(key[:10], root, prefix, n, row["status"], flush=True)
                    if row["status"] == "open" and len(prefix)-1 < args.depth:
                        for child in shared.children(prefix, parent, n):
                            visit(child)
                            if shared.witness_row(rows) or monotonic() >= deadline:
                                break
                if not shared.witness_row(rows) and not shared.covers((0,), rows, parent, n):
                    visit((0,))
            excluded = shared.covers((0,), rows, parent, n)
            positive = shared.witness_row(rows)
            require(not (excluded and positive), "Simultaneous witness and exclusion")
            status = "excluded" if excluded else "witness" if positive else "open" if rows else "unattempted"
            report.append(dict(shape=key, end=end, root=root, partner_edges=n, status=status,
                               prefixes=len(rows), joined_edges=97+n if positive else None))
    counts = Counter(r["status"] for r in report)
    if args.replay:
        suffix = "" if not args.ids else "-" + "-".join(args.ids)
        if set(args.ends) != {0, 1}:
            suffix += "-end" + str(args.ends[0])
        p.joins.save_json(HERE / ("partner-replay-" + str(n) + suffix + ".json"),
                          dict(ledger_sha256=file_hash(LEDGER) if LEDGER.exists() else None, pins=pins,
                               counts=counts, roots=report))
    print(dict(counts), flush=True)


if __name__ == "__main__":
    main()
