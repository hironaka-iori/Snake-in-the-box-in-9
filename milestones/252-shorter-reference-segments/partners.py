"""Search unrestricted opposite arms, share identical rooted cases, and replay their prefix covers."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "251-eighty-edge-segments"
sys.path.insert(0, str(PREVIOUS))
import partners251 as previous
from partners251 import read, require, file_hash, rooted, path_ok, shape

# Only the location of proof archives changes. All model, proof and witness
# operations come from the pinned previous module; preserve its base model.
previous.HERE = HERE
base_model = previous.model
POOL = HERE / "rooted-proofs.json"


def digest(data):
    return sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def canonical_root(seq):
    """First-occurrence relabelling of an oriented transition word, with its actual isometry."""
    src_axes = [(u ^ v).bit_length()-1 for u, v in zip(seq, seq[1:])]
    order = list(dict.fromkeys(src_axes))
    order += sorted(set(range(8))-set(order))
    axes = tuple(order.index(i) for i in range(8))
    table = previous.images(axes)
    parent = [table[v ^ seq[0]] for v in seq]
    word = bytes(axes[i] for i in src_axes)
    return sha256(word).hexdigest(), parent, list(axes)


def sources():
    catalogue = PREVIOUS / "census-72.json"
    upper_file = PREVIOUS / "profile-audit.json"
    bounds = read(upper_file)
    demand = PREVIOUS / "profiles.json"
    require(bounds["ledger_sha256"] == file_hash(demand), "Earlier profile ledger differs")
    old, archived = previous.known_parents()
    extra = list(read(catalogue)["new_shapes"])
    caps = {(r["id"], r["end"]): r["partner_upper"] for r in bounds["bounds"]}
    require(len(extra) == 3 and len(caps) == 6, "Unexpected Round 251 parent bounds")
    for row in extra:
        seq = row["path"]
        path_ok(seq, 8)
        require(sha256(shape(seq)).hexdigest() == row["id"], "Archived shape digest differs")
        archived.add(shape(seq))
        for end in (0, 1):
            k = row["id"], end
            old[k] = (rooted(seq, end), caps[k])
    pins = previous.pins(catalogue)
    pins.update({p.name: file_hash(p) for p in (Path(__file__), upper_file, demand)})
    return old, archived, pins


def anchored_model(prefix):
    def model(parent, length, rules):
        cnf, chosen = base_model(parent, length, rules)
        # The root has degree one, and selected internal vertices degree two.
        # Along an induced prefix starting at zero, these units fix its order.
        cnf.clauses.extend([chosen[v]] for v in prefix[1:])
        return cnf, chosen
    return model


def children(prefix, parent, length):
    if len(prefix) == length+1:
        return []
    occupied = set(parent) | set(prefix)
    return [prefix+(v,) for v in previous.joins.partner.NEIGHBOURS[prefix[-1]]
            if v not in occupied and all((v ^ u).bit_count() != 1 for u in prefix[:-1])]


def covers(prefix, rows, parent, length):
    r = rows.get(prefix)
    if r is None:
        return False
    if r["status"] in {"inherited", "excluded"}:
        return True
    if r["status"] != "open" or len(prefix) == length+1:
        return False
    return all(covers(q, rows, parent, length) for q in children(prefix, parent, length))


def witness_row(rows):
    return next((r for r in rows.values() if r["status"] == "witness"), None)


def check_prefix(parent, n, row):
    p = row["prefix"]
    path_ok(p, 8)
    require(p[0] == 0 and len(p) <= n+1 and set(p) & set(parent) == {0}, "Invalid rooted prefix")
    if row["status"] == "witness":
        require(row["partner"][:len(p)] == p, "Witness differs from the specified prefix")


def query_rows(entry, target):
    rows = {tuple(r["prefix"]): r for r in entry.get(str(target), [])}
    require(len(rows) == len(entry.get(str(target), [])), "Duplicate prefix")
    return rows


def search_one(entry, target, all_old, index, folder, exe, args, deadline, queries, persist):
    parent = entry["parent"]
    n = target-len(parent)
    rows = query_rows(entry, target)
    rules = None
    def visit(prefix):
        nonlocal rules
        if queries[0] >= args.max_queries or monotonic() >= deadline:
            return
        r = rows.get(prefix)
        old_open = r is not None and r["status"] == "open"
        if r is None or (old_open and args.retry_open and len(prefix)-1 == args.depth):
            if rules is None:
                rules = previous.active_cuts(previous.transfers(parent, all_old, index), n)
            previous.model = anchored_model(prefix)
            remaining = min(args.seconds, max(.01, deadline-monotonic()))
            answer = previous.solve(parent, n, rules, all_old, folder, exe, remaining, r)
            r = dict(prefix=list(prefix), **answer)
            check_prefix(parent, n, r)
            rows[prefix] = r
            queries[0] += 1
            entry[str(target)] = list(rows.values())
            persist()
            print(target, entry["shape"][:10], entry["root_key"][:10], prefix, r["status"], flush=True)
        if r["status"] == "open" and len(prefix)-1 < args.depth:
            for q in children(prefix, parent, n):
                visit(q)
                if witness_row(rows):
                    break
    if not witness_row(rows) and not covers((0,), rows, parent, n):
        visit((0,))


def replay_one(entry, target, all_old, folder, exe):
    parent = entry["parent"]
    length = target-len(parent)
    rows = query_rows(entry, target)
    for prefix, row in rows.items():
        require(len(prefix)==1 or prefix[:-1] in rows, "Missing ancestor in prefix tree")
        check_prefix(parent, length, row)
        previous.model = anchored_model(prefix)
        previous.replay(parent, length, row, all_old, folder, exe)
    return rows


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--core", type=int, required=True)
    cli.add_argument("--target", type=int, choices=(191,192), default=192)
    cli.add_argument("--direct", action="store_true", help="Search 192 without first probing 191")
    cli.add_argument("--seconds", type=float, default=6)
    cli.add_argument("--total", type=float, default=170)
    cli.add_argument("--max-queries", type=int, default=10000)
    cli.add_argument("--depth", type=int, default=0)
    cli.add_argument("--id", help="Unique initial characters of a shape ID")
    cli.add_argument("--end", type=int, choices=(0,1))
    cli.add_argument("--retry-open", action="store_true")
    cli.add_argument("--replay", action="store_true")
    args = cli.parse_args()
    require(0<=args.depth<=8 and min(args.seconds,args.total,args.max_queries)>0, "Invalid resource limit")
    source = HERE/f"census-{args.core}.json"
    catalogue = read(source)
    all_old, archived, pins = sources()
    archived_ids = {sha256(k).hexdigest() for k in archived}
    ids = [r["id"] for r in catalogue["new_shapes"]]
    require(len(ids)==len(set(ids)) and sorted(set(catalogue["all_ids"])-archived_ids)==sorted(set(ids)-archived_ids),
            "Incomplete new-shape list")
    pool = read(POOL) if POOL.exists() else dict(pins=pins, roots={})
    require(pool["pins"]==pins, "Shared proof dependencies differ")
    def persist():
        previous.joins.save_json(POOL, pool)
    index = {} if args.replay else previous.placement_index(all_old)
    report = []
    deadline = monotonic()+args.total
    queries = [0]
    selected_ids = [k for k in ids if not args.id or k.startswith(args.id)]
    if args.id: require(len(selected_ids)==1, "Shape missing or ambiguous")
    with TemporaryDirectory(prefix="q9-root252-") as temporary:
        folder = Path(temporary)
        exe = folder/"VerifyLrat.exe"
        subprocess.run([str(previous.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),
                        str(previous.joins.CHECKER)],check=True,capture_output=True,timeout=45)
        checked_keys = set()
        for row in catalogue["new_shapes"]:
            path = row["path"]
            path_ok(path,8)
            label = row["id"]
            require(label==sha256(shape(path)).hexdigest() and len(path)-1==row["edges"]
                    and 96<=row["edges"]<=98, "Invalid census representative")
            if label in archived_ids or label not in selected_ids:
                continue
            for end, order in enumerate((path,path[::-1])):
                if args.end is not None and args.end != end:
                    continue
                root_key, parent, axes = canonical_root(order)
                entry = pool["roots"].setdefault(root_key,dict(root_key=root_key,shape=label,parent=parent))
                require(entry["root_key"]==root_key and entry["parent"]==parent and entry["shape"]==label,
                        "Incompatible previously stored rooted word")
                targets = [191] if args.target==191 else [191,192]
                shortest_excluded = None
                longest_witness = None
                for t in targets:
                    if args.replay and (root_key,t) not in checked_keys:
                        replay_one(entry,t,all_old,folder,exe)
                        checked_keys.add((root_key,t))
                    elif not args.replay and shortest_excluded is None and (not args.direct or t==args.target):
                        search_one(entry,t,all_old,index,folder,exe,args,deadline,queries,persist)
                    rows = query_rows(entry,t)
                    if covers((0,),rows,parent,t-len(parent)):
                        shortest_excluded = shortest_excluded or t
                    if witness_row(rows): longest_witness=t
                require(longest_witness is None or shortest_excluded is None or longest_witness<shortest_excluded,
                        "Conflicting witness and exclusion")
                status = ("excluded" if shortest_excluded is not None else
                          "witness" if longest_witness==args.target else "open")
                report.append(dict(id=label,end=end,root=order[0],root_key=root_key,axes=axes,
                                   status=status,shortest_excluded=shortest_excluded,
                                   longest_witness=longest_witness,root_record_sha256=digest(entry)))
    if args.replay:
        complete = len(report)==2*len(set(ids)-archived_ids)
        counts = Counter(r["status"] for r in report)
        suffix = ("-"+args.id if args.id else "")+(f"-end{args.end}" if args.end is not None else "")
        result=dict(census_sha256=file_hash(source),target=args.target,archived_classes=len(archived_ids),
                    all_new_endpoints_reviewed=complete,all_excluded=complete and counts["excluded"]==len(report),
                    counts=counts,endpoints=report,dependencies=pins)
        previous.joins.save_json(HERE/f"replay-{args.core}-{args.target}{suffix}.json",result)
        print("New rooted endpoints",dict(counts),flush=True)


if __name__=="__main__":
    main()
