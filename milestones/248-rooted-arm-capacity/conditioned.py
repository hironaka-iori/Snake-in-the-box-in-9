"""Rooted 95-edge partner search with exact local linear-forest occupancy tables."""
from array import array
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import gzip
import json
import subprocess
import sys


HERE = Path(__file__).resolve().parent
LAST = HERE.parent / "247-relative-middle-placements"
sys.path.insert(0, str(LAST))
import partner
import lifts
import cert_replay as audit


N = partner.NEIGHBOURS
LOCAL = [sum(1 << (v ^ (1 << i)) for i in range(4)) for v in range(16)]
EVEN = sum(1 << v for v in range(16) if v.bit_count() % 2 == 0)
MASK = (1 << 16)-1
STRIDE = 128   # There are only 80 available vertices on either parity side.


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length()-1
        mask ^= low


@lru_cache(maxsize=1)
def forest_degrees():
    """For each Q4 subset cache its local degree-0/1 vertices; -1 marks a non-forest."""
    zero = array("i", [-1]) * (1 << 16)
    one = array("i", [0]) * (1 << 16)
    for mask in range(1 << 16):
        isolated = leaves = 0
        for v in bits(mask):
            degree = (LOCAL[v] & mask).bit_count()
            if degree > 2:
                break
            if degree == 0:
                isolated |= 1 << v
            elif degree == 1:
                leaves |= 1 << v
        else:
            # In a graph with maximum degree two, a component contains a cycle
            # exactly when none of its vertices can be reached from a leaf or isolate.
            reached = frontier = isolated | leaves
            while frontier and reached != mask:
                adjacent = 0
                for v in bits(frontier):
                    adjacent |= LOCAL[v]
                frontier = adjacent & mask & ~reached
                reached |= frontier
            if reached == mask:
                zero[mask], one[mask] = isolated, leaves
    return zero, one


def component(domain, root):
    seen = {root}
    stack = [root]
    while stack:
        add = domain.intersection(N[stack.pop()]) - seen
        seen.update(add)
        stack.extend(add)
    return seen


def domain_after_prefix(parent, prefix):
    """Remove chords to the fixed initial segment and iteratively impossible vertices."""
    partner.validate_prefix(parent, prefix)
    fixed = set(prefix)
    allowed = set(range(256))-set(parent[1:])
    for v in prefix[:-1]:
        allowed.difference_update(set(N[v])-fixed)
    while fixed <= allowed:
        # Once the tip is reached, an extension cannot pass back through an earlier vertex.
        tail = component(allowed-set(prefix[:-1]), prefix[-1])
        here = fixed | tail
        bad = {v for v in here if len(here.intersection(N[v])) <
               (2 if v != 0 and (v in fixed or v.bit_count()%2 == 0) else 1)}
        if not bad and here == allowed:
            break
        allowed = here-bad
    return allowed


def face_table(vertices, domain, fixed):
    valid = sum(1 << i for i,v in enumerate(vertices) if v in domain)
    must = sum(1 << i for i,v in enumerate(vertices) if v in fixed)
    outside = [set(N[v])-set(vertices) for v in vertices]
    bad = [0, 0, 0]
    last = [0, 0, 0]
    for i,v in enumerate(vertices):
        if v not in domain:
            continue
        lower = 1 if v == 0 or (v not in fixed and v.bit_count()%2) else 2
        upper = 1 if v == 0 else 2
        for d in (0, 1, 2):
            possible = d + len(outside[i] & domain)
            compulsory = d + len(outside[i] & fixed)
            if possible < lower or compulsory > upper:
                bad[d] |= 1 << i
            if possible == 1 and v.bit_count()%2:
                last[d] |= 1 << i
    zero, one = forest_degrees()
    parity = EVEN if vertices[0].bit_count()%2 == 0 else MASK ^ EVEN
    pairs = set()
    free = sub = valid & ~must
    while True:
        s = sub | must
        z, o = zero[s], one[s]
        if z >= 0:
            t = s & ~(z | o)
            if not (bad[0]&z or bad[1]&o or bad[2]&t):
                forced_ends = (last[0]&z) | (last[1]&o) | (last[2]&t)
                if forced_ends.bit_count() <= 1:
                    e = (s & parity).bit_count()
                    pairs.add((e, s.bit_count()-e))
        if sub == 0:
            return pairs
        sub = (sub-1) & free


def partition(axes, domain, fixed):
    offsets = [0]
    for a in axes:
        offsets += [x | (1 << a) for x in offsets]
    groups = []
    for base in range(256):
        if base & offsets[-1] == 0:
            vertices = [base | offset for offset in offsets]
            groups.append((vertices, face_table(vertices, domain, fixed)))
    return groups


def reachable(groups):
    """Bit e+128o records an attainable sum (e,o) across independent blocks."""
    totals = 1
    for _, pairs in groups:
        new = 0
        for e,o in pairs:
            new |= totals << (e + STRIDE*o)
        totals = new
    return totals


def attainable(table, e, o):
    return e >= 0 and o >= 0 and (table >> (e + STRIDE*o)) & 1


def exact_count_negation(counter, count):
    return ([-counter[count-1]] if count else []) + ([counter[count]] if count < len(counter) else [])


def add_partition(cnf, chosen, groups, domain):
    deficits = []
    maximum_total = 0
    tables = []
    for i, (vertices, possible) in enumerate(groups):
        others = reachable(groups[:i]+groups[i+1:])
        extendable = {(e,o) for e,o in possible if attainable(others, 48-e, 48-o)}
        if not extendable:
            raise ValueError("Partition previously passed the total-quota check")
        local = [[chosen[v] for v in vertices if v in domain and v.bit_count()%2 == k] for k in (0,1)]
        counts = [lifts.unary(cnf, variables) for variables in local]
        for e in range(len(local[0])+1):
            for o in range(len(local[1])+1):
                if (e,o) not in extendable:
                    cnf.clauses.append(exact_count_negation(counts[0],e)+exact_count_negation(counts[1],o))
        maximum = max(e+o for e,o in extendable)
        occupancy = lifts.unary(cnf, local[0]+local[1])
        if maximum < len(occupancy):
            cnf.clauses.append([-occupancy[maximum]])
        deficits.extend(-v for v in occupancy[:maximum])
        maximum_total += maximum
        tables.append(dict(base=vertices[0], possible=sorted(possible), extendable=sorted(extendable)))
    # Each true deficit literal is one vertex below the face capacity. There
    # must be 96 selected vertices globally, so their total deficit is fixed.
    cnf.at_most(deficits, maximum_total-96)
    return dict(maximum_total=maximum_total, deficit_budget=maximum_total-96, faces=tables)


def articulation_cuts(cnf, chosen, domain):
    count = 0
    for v in sorted(domain-{0}):
        remainder = domain-{v}
        away = remainder-component(remainder,0)
        used = []
        while away:
            branch = component(away,min(away))
            away -= branch
            indicator = cnf.variable()
            for u in sorted(branch):
                cnf.clauses.append([-chosen[u],indicator])
            cnf.clauses.append([-indicator,chosen[v]])
            used.append(indicator)
            count += 1
        cnf.clauses.extend([-a,-b] for a,b in combinations(used,2))
    return count


def encode(parent, prefix, top=3):
    if len(prefix) >= 96:
        raise ValueError("This conditioning method expects a proper prefix")
    cnf, chosen = partner.encode(parent, prefix)
    domain = domain_after_prefix(parent,prefix)
    details = dict(domain=sorted(domain), partitions=[])
    if not set(prefix) <= domain:
        cnf.clauses.append([])
        details["pruned_prefix"] = True
        return cnf, chosen, details
    for v in sorted(set(chosen)-domain):
        cnf.clauses.append([-chosen[v]])
    details["articulation_branches"] = articulation_cuts(cnf,chosen,domain)
    candidates = []
    for axes in combinations(range(8),4):
        groups = partition(axes,domain,set(prefix))
        if not attainable(reachable(groups),48,48):
            details["partition_obstruction"] = dict(axes=axes, faces=[
                dict(base=vs[0], possible=sorted(pairs)) for vs,pairs in groups])
            cnf.clauses.append([])
            return cnf, chosen, details
        rank = (sum(max(e+o for e,o in pairs) for _,pairs in groups),
                sum(len(pairs) for _,pairs in groups), axes)
        candidates.append((rank,groups))
    for (_,_,axes),groups in sorted(candidates,key=lambda item:item[0])[:top]:
        details["partitions"].append(dict(axes=axes, **add_partition(cnf,chosen,groups,domain)))
    return cnf,chosen,details


def proof_archive(source):
    raw = partner.digest(source)
    dest = HERE/"conditioned-proofs"/(raw+".lrat.gz")
    dest.parent.mkdir(exist_ok=True)
    if not dest.exists():
        tmp = dest.with_suffix(".tmp")
        with source.open("rb") as inp, tmp.open("wb") as stream:
            with gzip.GzipFile(filename="", fileobj=stream, mode="wb", compresslevel=2, mtime=0) as out:
                for block in iter(lambda:inp.read(65536),b""):
                    out.write(block)
        tmp.replace(dest)
    return dict(proof=dest.relative_to(HERE).as_posix(),lrat_sha256=raw,lrat_bytes=source.stat().st_size)


def solve(parent,prefix,folder,seconds,top):
    cnf,chosen,details = encode(parent,prefix,top)
    record = dict(prefix=list(prefix), conditioning=details, attempts=[], status="unknown")
    if "partition_obstruction" in details or details.get("pruned_prefix"):
        record["status"] = "local_exclusion"
        return record
    filename,proof = folder/"case.cnf",folder/"proof.lrat"
    remain = seconds
    while remain > 0:
        if proof.exists():
            proof.unlink()
        row = dict(cnf_sha256=cnf.save(filename),variables=cnf.count,clauses=len(cnf.clauses))
        record["attempts"].append(row)
        begin = monotonic()
        try:
            proc = subprocess.run([str(partner.SOLVER),"--plain","-q","--lrat","--no-binary",
                                   str(filename),str(proof)],capture_output=True,timeout=remain)
        except subprocess.TimeoutExpired:
            row.update(outcome="timeout",seconds=monotonic()-begin)
            return record
        row["seconds"] = monotonic()-begin
        remain -= row["seconds"]
        if proc.returncode == 20 and b"s UNSATISFIABLE" in proc.stdout:
            if not proof.is_file() or not proof.stat().st_size:
                raise ValueError("Absent plain LRAT proof")
            row.update(outcome="UNSAT",**proof_archive(proof))
            record["status"]="solver_exclusion"
            return record
        if proc.returncode != 10 or b"s SATISFIABLE" not in proc.stdout:
            raise RuntimeError((proc.returncode,proc.stdout[-300:],proc.stderr[-300:]))
        true = {int(w) for line in proc.stdout.splitlines() if line.startswith(b"v ")
                for w in line.split()[1:] if int(w)>0}
        selected = {v for v,lit in chosen.items() if lit in true}
        companion,joined,cycles = partner.extract(parent,prefix,selected)
        if joined is not None:
            row["outcome"]="witness"
            record.update(status="witness",partner=companion,q9_path=joined)
            return record
        row.update(outcome="disconnected",cycles=cycles)
        cnf.clauses.extend(partner.cycle_clause(chosen,cycle) for cycle in cycles)
    return record


def open_cases():
    source = LAST/"partner-children-summary.json"
    rec = json.loads(source.read_bytes())
    if rec["replay_error"] is not None or rec["pending"] != 0:
        raise ValueError("Incomplete incoming child inventory")
    children = LAST/"partner-children.json"
    if rec["ledger_sha256"] != partner.digest(children):
        raise ValueError("Incoming child ledger changed")
    rows = json.loads(children.read_bytes())["records"]
    unknown = {(r["class_id"],r["endpoint"],tuple(r["prefix"])) for r in rows if r["status"]=="unknown"}
    ordered = [(r["class_id"],r["endpoint"],(0,v)) for r in rec["endpoint_cases"] for v in r.get("unknown",[])]
    if len(ordered) != 16 or set(ordered) != unknown:
        raise ValueError("Incoming uncovered prefixes differ")
    return ordered


def save(path,data):
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    tmp.replace(path)


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--seconds",type=float,default=4)
    cli.add_argument("--partitions",type=int,default=3)
    cli.add_argument("--depth",type=int,default=1,help="Largest queried prefix length in edges")
    cli.add_argument("--nodes",type=int,default=100000,help="Maximum new queries in this invocation")
    cli.add_argument("--output",type=Path,default=HERE/"conditioned.json")
    args=cli.parse_args()
    if not (args.seconds>0 and 0<=args.partitions<=70 and 1<=args.depth<=93 and args.nodes>0):
        cli.error("Invalid run settings")
    parents=partner.parent_arms()
    roots=open_cases()
    old=json.loads((LAST/"partners.json").read_bytes())["pins"]
    if any(partner.digest(p)!=old[p.name] for p in
           [partner.SOLVER,LAST/"partner.py",partner.PREV/"free_outer.py",partner.SOURCE/"arc_sat.py"]):
        raise ValueError("Frozen solver or inherited path model changed")
    files=[Path(__file__),LAST/"lifts.py",LAST/"partner.py",partner.PREV/"free_outer.py",
           partner.SOURCE/"arc_sat.py",LAST/"partner-children-summary.json",LAST/"partner-children.json",
           partner.PREV/"comparison.json",partner.PREV/"arm-structure.json",partner.SOLVER]
    pins={p.name:partner.digest(p) for p in files}
    settings=dict(seconds=args.seconds,partitions=args.partitions)
    if args.output.exists():
        data=json.loads(args.output.read_bytes())
        if data["pins"]!=pins or data["settings"]!=settings:
            raise ValueError("Ledger source pins or per-query settings changed")
    else:
        data=dict(pins=pins,settings=settings,initial_prefixes=roots,records=[])
    records={(r["class_id"],r["endpoint"],tuple(r["prefix"])):r for r in data["records"]}
    if len(records)!=len(data["records"]):
        raise ValueError("Duplicate query in ledger")
    queue=list(roots)
    count=0
    with TemporaryDirectory(prefix="q9-conditioned-") as tmp:
        for i,e,prefix in queue:
            parent=partner.rooted_parent(parents[i],e)
            k=i,e,prefix
            if k not in records:
                if count>=args.nodes:
                    break
                r=dict(class_id=i,endpoint=e,**solve(parent,prefix,Path(tmp),args.seconds,args.partitions))
                records[k]=r
                data["records"].append(r)
                save(args.output,data)
                count+=1
                print(i,e,prefix,r["status"],flush=True)
            status=records[k]["status"]
            if status=="witness":
                break
            if status=="unknown" and len(prefix)-1<args.depth:
                queue.extend((i,e,prefix+(v,)) for v in partner.next_vertices(parent,prefix))
    print("Saved status counts:",dict(Counter(r["status"] for r in records.values())))


if __name__=="__main__":
    main()
