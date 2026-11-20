"""Reconstruct the partner ledgers, fixed-root coverage and subpath implications."""
from collections import Counter, defaultdict
import gzip
from hashlib import sha256
import json
from pathlib import Path
import re
from tempfile import TemporaryDirectory

import joins

HERE = joins.HERE
OLD = joins.LAST
SOURCE = joins.partner.PREV
INPUTS = {}


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def file_hash(path, opener=open):
    h = sha256()
    with opener(path, "rb") as f:
        for block in iter(lambda: f.read(131072), b""):
            h.update(block)
    return h.hexdigest()


def read(path):
    raw = path.read_bytes()
    INPUTS[path.relative_to(HERE.parents[1]).as_posix()] = sha256(raw).hexdigest()
    return json.loads(raw)


def path_ok(word, dimension):
    require(word and len(word) == len(set(word)) and all(0 <= v < 2**dimension for v in word),
            "Empty path, repeated vertex, or vertex outside cube")
    for j, v in enumerate(word):
        for i in range(j):
            require(((v ^ word[i]).bit_count() == 1) == (i + 1 == j), ("Induced adjacency", i, j))
    return len(word) * (len(word) - 1) // 2


def rooted(path, end):
    order = path if end == 0 else path[::-1]
    return [v ^ order[0] for v in order]


def axis_map(a, b):
    """An ordered, root-preserving cube isometry, from transition letters."""
    if len(a) != len(b) or a[0] != 0 or b[0] != 0:
        return None
    forward, inverse = {}, {}
    for x, y, u, v in zip(a, a[1:], b, b[1:]):
        i, j = (x ^ y).bit_length()-1, (u ^ v).bit_length()-1
        if forward.setdefault(i, j) != j or inverse.setdefault(j, i) != i:
            return None
    free = set(range(8))
    forward.update(zip(sorted(free - forward.keys()), sorted(free - inverse.keys())))
    axes = tuple(forward[i] for i in range(8))
    require(len(set(axes)) == 8 and
            [sum(1 << axes[t] for t in range(8) if x & (1 << t)) for x in a] == b,
            "Transition correspondence does not reconstruct the vertices")
    return axes


def verified_partner(parent, w, length):
    arm = w["partner"]
    combined = parent[::-1] + [256 + v for v in arm]
    require(len(arm) == length + 1 and arm[0] == 0 and set(arm) & set(parent) == {0}
            and w["joined"] == combined and w["joined_edges"] == len(combined) - 1
            and w["partner_edges"] == length, "Partner does not yield the claimed lift")
    counts = dict(parent=path_ok(parent, 8), partner=path_ok(arm, 8), joined=path_ok(combined, 9))
    require(counts == w["all_pairs"], "Mismatched pair counts")


def check_cycle(vertices, chosen):
    sites = set(vertices)
    require(len(sites) == len(vertices) and sites and sites <= chosen.keys(), "Invalid cycle sites")
    ns = {v: {w for w in sites if (w ^ v).bit_count() == 1} for v in sites}
    require(all(len(adj) == 2 for adj in ns.values()), "Cycle degree")
    seen, todo = set(), [next(iter(sites))]
    while todo:
        u = todo.pop()
        if u not in seen:
            seen.add(u)
            todo.extend(ns[u] - seen)
    require(seen == sites, "Disconnected cycle")
    return [-chosen[v] for v in sorted(sites)]


def row_check(row, parent, length, formula, files):
    prefix = row["prefix"]
    require(prefix[0] == 0 and set(parent) & set(prefix) == {0} and len(prefix) <= length + 1,
            "Wrong rooted case")
    path_ok(prefix, 8)
    if length == 95:
        cnf, chosen = joins.partner.encode(parent, prefix)
    elif length == 94:
        cnf, chosen = joins.encode94(parent, prefix)
    else:
        cnf, chosen = joins.opposite.encode(parent, length, prefix)
    trace = []
    attempts = row["attempts"]
    status = row["status"]
    require(status in {"excluded", "witness", "open"} and (attempts or status == "open"),
            "Malformed query status")
    for j, step in enumerate(attempts):
        digest = cnf.save(formula)
        require(step["cnf_sha256"] == digest and step["clauses"] == len(cnf.clauses)
                and step["variables"] == cnf.count, "Regenerated formula differs")
        last = j == len(attempts) - 1
        kind = step["outcome"]
        if kind == "disconnected":
            require(step["cycles"] and (not last or status == "open"), "Improper intermediate model")
            for cycle in step["cycles"]:
                cnf.clauses.append(check_cycle(cycle, chosen))
                trace.append(cycle)
        elif kind == "verified_unsat" and last and status == "excluded":
            expected = "proofs/" + digest + ".lrat.gz"
            require(row["proof"] == expected and digest == row["cnf_sha256"], "Proof binding")
            receipt = re.fullmatch(r"VERIFIED UNSAT variables=(\d+) input_clauses=(\d+) additions=(\d+) "
                                   r"deleted_clauses=(\d+) hints=(\d+) empty_id=(\d+)", row["checker"])
            require(receipt and int(receipt[1]) == cnf.count and int(receipt[2]) == len(cnf.clauses)
                    and int(receipt[3]) > 0 and int(receipt[6]) > len(cnf.clauses), "Checker receipt")
            if expected not in files:
                files[expected] = (file_hash(HERE/expected), file_hash(HERE/expected, gzip.open))
            require(files[expected] == (row["gzip_sha256"], row["raw_sha256"]), "Proof hash")
        elif kind == "connected" and last and status == "witness":
            verified_partner(parent, row, length)
            require(row["partner"][:len(prefix)] == prefix, "Witness prefix")
        else:
            require(kind == "timeout" and last and status == "open", "Invalid final outcome")
    require(row["cycles"] == trace, "Cycle cut history differs")


def leaves(parent, length, excluded, attempted):
    """Branch solely on cube adjacency, forbidden parent and actual prefix chords."""
    def visit(p):
        if p in excluded:
            return []
        if p not in attempted or len(p) >= length + 1:
            return [p]
        used = set(parent) | set(p)
        possible = [v for v in range(256) if v not in used and (v ^ p[-1]).bit_count() == 1
                    and all((v ^ u).bit_count() != 1 for u in p[:-1])]
        return [q for v in possible for q in visit(p + (v,))]
    return visit((0,))


def main():
    previous = read(joins.INVENTORY)
    bank = read(SOURCE/"donors.json")["shapes"]
    require(file_hash(SOURCE/"donors.json") == previous["source_sha256"], "Donor source pin")
    inventory = {r["donor_index"]: r for r in previous["rows"]}
    require(set(inventory) == {i for i, d in enumerate(bank) if len(d["path"]) >= 97}
            and len(inventory) == len(previous["rows"]), "Long donor index coverage")
    parents = {}
    for i, row in inventory.items():
        path = bank[i]["path"]
        require(path == row["path"] and len(path)-1 == row["edges"]
                and [path[0],path[-1]] == row["endpoints"] and row["required_partner"] == 192-len(path),
                ("Inventory", i))
        path_ok(path, 8)
        for e in (0, 1):
            parents[i,e] = rooted(path,e)
    todo = {i for i,r in inventory.items() if r["edges"] == 96 and r["previous_96_class"] is None}
    require(sorted(todo) == previous["remaining_96"] and
            sorted(i for i,r in inventory.items() if r["edges"] == 97) == previous["length_97"],
            "Inventory classification")
    known = [HERE/"joins.py", joins.INVENTORY, SOURCE/"donors.json", OLD/"opposite.py",
             OLD/"endpoint94.py", OLD/"certify.py", Path(joins.partner.__file__), SOURCE/"free_outer.py",
             joins.partner.SOURCE/"arc_sat.py", joins.CHECKER, joins.COMPILER, joins.partner.SOLVER]
    pins = {p.name: file_hash(p) for p in known}
    groups = defaultdict(list)
    lower = defaultdict(int)
    files = {}
    lengths = set()
    with TemporaryDirectory(prefix="snake249-audit-") as tmp:
        formula = Path(tmp)/"reconstructed.cnf"
        for ledger in sorted(HERE.glob("partners-*.json")):
            data = read(ledger)
            n = data["length"]
            require(ledger.name == f"partners-{n}.json" and 1 <= n <= 95 and n not in lengths
                    and data["pins"] == pins, "Input provenance or length")
            lengths.add(n)
            for r in data["records"]:
                key = r["donor"], r["endpoint"]
                require(key[0] in todo and key in parents, ("Case outside input set",key))
                row_check(r, parents[key], n, formula, files)
                groups[key,n].append(r)
                if r["status"] == "witness":
                    lower[key] = max(n,lower[key])
    if (HERE/"witnesses.json").exists():
        w = read(HERE/"witnesses.json")
        expected = {name:pins[name] for name in ("joins.py","parents.json","donors.json","opposite.py",
                                                  "endpoint94.py","partner.py",joins.partner.SOLVER.name)}
        expected["witnesses.py"] = file_hash(HERE/"witnesses.py")
        require(w["pins"] == expected, "Witness provenance")
        for row in w["records"]:
            key = tuple(row["case"])
            require(key[0] in todo and row["parent"] == parents[key],"Witness parent")
            best = row["best"]
            verified_partner(parents[key],best,best["partner_edges"])
            lower[key] = max(best["partner_edges"],lower[key])
    bounds = defaultdict(list)
    summary = []
    for key in sorted(k for k in parents if k[0] in todo):
        prior_exclusions, split = set(), set()
        for n in sorted(lengths):
            queries = groups[key,n]
            attempted = {tuple(q["prefix"]) for q in queries}
            excluded = {tuple(q["prefix"]) for q in queries if q["status"] == "excluded"}
            direct = leaves(parents[key], n, excluded, attempted)
            prior_exclusions.update(excluded)
            split.update(attempted)
            pending = leaves(parents[key], n, prior_exclusions, split)
            if not pending:
                require(lower[key] < n, ("Conflicting witness and exclusion",key,n))
                bounds[key].append(dict(upper=n-1, basis="direct" if not direct else "prefixes at shorter lengths"))
            summary.append(dict(donor=key[0],endpoint=key[1],length=n,queries=len(queries),
                                outcomes=dict(Counter(r["status"] for r in queries)),
                                direct_open=direct,open_after_shorter_exclusions=pending))
    archived = read(OLD/"aggregate.json")
    opposites = read(OLD/"opposite-audit.json")
    deep = read(OLD/"deep-opposite.json")
    attained = read(OLD/"attainers.json")
    opposite_paths = read(OLD/"opposite.json")
    examples = read(SOURCE/"comparison.json")
    require(archived["coverage95"]["covered_first_steps"] == 70 and archived["attainers"]["complete"],
            "Round 248 result missing")
    opposite_upper = {r["class_id"]:r["upper"] for r in opposites["classes"]}
    opposite_upper[deep["class_id"]] = min(opposite_upper[deep["class_id"]],deep["upper"])
    saved_paths = {(r["class_id"],0): r["paths"][0]["path"] for r in attained["records"]}
    saved_paths.update({(r["class_id"],1): r["lower_witness"]["partner"] for r in opposite_paths["records"]})
    saved_paths[deep["class_id"],deep["endpoint"]] = deep["lower_witness"]["partner"]
    for i,r in inventory.items():
        cl = r["previous_96_class"]
        if cl is None:
            continue
        saved = next(z["long"] for z in examples["one_crossing_pairs"] if z["seed"] == cl)
        for end in (0,1):
            orientations = [e for e in (0,1) if axis_map(rooted(saved,e),parents[i,end]) is not None]
            require(orientations, "Archived orientation failed")
            for e in orientations:
                bound = 94 if e == 0 else opposite_upper[cl]
                bounds[i,end].append(dict(upper=bound,basis=f"Round 248 class {cl}, endpoint {e}"))
                axes = axis_map(rooted(saved,e),parents[i,end])
                path = [sum(1 << axes[t] for t in range(8) if v & (1 << t)) for v in saved_paths[cl,e]]
                require(path[0] == 0 and set(path) & set(parents[i,end]) == {0},"Imported witness")
                path_ok(parents[i,end][::-1] + [256+v for v in path],9)
                lower[i,end] = max(lower[i,end],len(path)-1)
    old98 = read(HERE.parent/"222-prefix-certificates"/"data"/"completion.json")
    require(inventory[20]["path"] == examples["examples"]["optimal_98"]["path"] and
            old98["fixed_parent_93_edge_exclusion_both_roots"],"Round 222 parent or receipt")
    for e in (0,1):
        bounds[20,e].append(dict(upper=old98["arbitrary_compatible_partner_max_edges"],basis="Round 222"))
    transfers = []
    for key, target in sorted(parents.items()):
        matches = []
        for source, statements in sorted(bounds.items()):
            if source == key or len(parents[source]) > len(target):
                continue
            small = parents[source]
            for start in range(len(target)-len(small)+1):
                segment = target[start:start+len(small)]
                for reverse in (False,True):
                    oriented = segment[::-1] if reverse else segment
                    if oriented[0] != 0:
                        continue
                    axes = axis_map(small,oriented)
                    if axes is not None:
                        matches.append(dict(source=source,start=start,reversed=reverse,axes=axes,
                                            upper=min(s["upper"] for s in statements)))
        direct_bounds = bounds.get(key,[])
        upper = min([98]+[s["upper"] for s in direct_bounds]+[s["upper"] for s in matches])
        require(lower[key] <= upper, ("Inconsistent transferred upper bound",key))
        target_length = 192-len(target)
        transfers.append(dict(donor=key[0],endpoint=key[1],edges=len(target)-1,target=target_length,
                              direct_bounds=direct_bounds,transfers=matches,lower=lower[key],upper=upper,
                              excluded_at_192=upper<target_length))
        print(key,"partner",lower[key],upper,"192 target",target_length,flush=True)
    out = dict(inputs=INPUTS,source_sha256=file_hash(Path(__file__)),queries=sum(map(len,groups.values())),
               verified_archives=len(files),scope="Input hashes, formula reconstruction, verified LRAT receipt binding, "
               "compressed and uncompressed hashes, independent induced-path and prefix-cover checks. "
               "LRAT resolution traces were replayed in the originating search.",
               coverage=summary,cases=transfers)
    joins.save_json(HERE/"audit.json",out)


if __name__ == "__main__":
    main()
