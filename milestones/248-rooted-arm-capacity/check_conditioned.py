"""Check finite face tables by ordinary vertex sets and replay conditioned LRAT."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess

import conditioned as search


def components(points):
    todo = set(points)
    groups = []
    while todo:
        root = next(iter(todo))
        group, pending = {root}, [root]
        todo.remove(root)
        while pending:
            for v in search.N[pending.pop()]:
                if v in todo:
                    todo.remove(v)
                    group.add(v)
                    pending.append(v)
        groups.append(group)
    return groups


def check_domain(parent, prefix):
    fixed = set(prefix)
    possible = {v for v in range(256) if v not in parent or v == 0}
    possible = {v for v in possible if v in fixed or
                all((v^w).bit_count() != 1 for w in prefix[:-1])}
    while fixed <= possible:
        tail = next(g for g in components(possible-set(prefix[:-1])) if prefix[-1] in g)
        here = fixed | tail
        keep = {v for v in here if len(set(search.N[v]) & here) >=
                (2 if v != 0 and (v in fixed or v.bit_count()%2 == 0) else 1)}
        if keep == possible:
            break
        possible = keep
    return possible


def local_pairs(face, domain, fixed):
    compulsory = face & fixed
    optional = sorted((face & domain)-compulsory)
    exterior_min = {v: len(set(search.N[v]) & (fixed-face)) for v in face}
    exterior_max = {v: len(set(search.N[v]) & (domain-face)) for v in face}
    local_ns = {v: set(search.N[v]) & face for v in face}
    pairs = set()
    for k in range(len(optional)+1):
        for optional_pick in combinations(optional,k):
            picked = compulsory.union(optional_pick)
            ends = edges_twice = 0
            for v in picked:
                d = len(picked & local_ns[v])
                edges_twice += d
                lo = 2 if v != 0 and (v in fixed or v.bit_count()%2 == 0) else 1
                hi = 1 if v == 0 else 2
                if d > 2 or d+exterior_min[v] > hi or d+exterior_max[v] < lo:
                    break
                if v.bit_count()%2 and d+exterior_max[v] == 1:
                    ends += 1
                    if ends > 1:
                        break
            else:
                # For simple undirected graphs, |E| = |V|-components iff a forest.
                if edges_twice == 2*(len(picked)-len(components(picked))):
                    odd = sum(v.bit_count()%2 for v in picked)
                    pairs.add((len(picked)-odd,odd))
    return pairs


def sums(groups):
    result = {(0,0)}
    for pairs in groups:
        result = {(a+c,b+d) for a,b in result for c,d in pairs if a+c<=48 and b+d<=48}
    return result


def partial_sums(groups):
    layers = [{(0,0)}]
    for pairs in groups:
        layers.append({(a+c,b+d) for a,b in layers[-1] for c,d in pairs if a+c<=48 and b+d<=48})
    return layers


def geometry(parent,prefix,details):
    domain = check_domain(parent,prefix)
    if set(details["domain"]) != domain:
        raise ValueError("The independent forced-prefix domain differs")
    if not set(prefix) <= domain:
        if not details.get("pruned_prefix"):
            raise ValueError("Expected exhausted prefix")
        return 0
    expected_branches = sum(len(components(domain-{v}))-1 for v in domain-{0})
    if expected_branches != details["articulation_branches"]:
        raise ValueError("Articulation partition mismatch")
    obstruction = details.get("partition_obstruction")
    cuts = [obstruction] if obstruction else details["partitions"]
    checked = 0
    for cut in cuts:
        axes = cut["axes"]
        if len(set(axes)) != 4 or not set(axes) <= set(range(8)):
            raise ValueError("Incorrect Q4 axes")
        mask = sum(1<<i for i in axes)
        entire = [{v for v in range(256) if v & ~mask == base} for base in range(256) if not base & mask]
        faces = cut["faces"]
        if [min(g) for g in entire] != [r["base"] for r in faces]:
            raise ValueError("Incorrect disjoint face cover")
        pairs = [local_pairs(face,domain,set(prefix)) for face in entire]
        if any(sorted(values) != sorted(map(tuple,row["possible"])) for values,row in zip(pairs,faces)):
            raise ValueError("Locally feasible parity counts differ")
        if obstruction:
            if (48,48) in sums(pairs):
                raise ValueError("Alleged parity obstruction permits the quota")
        else:
            maximum = 0
            left, right = partial_sums(pairs), partial_sums(list(reversed(pairs)))
            for i,face in enumerate(faces):
                a,b = sorted((left[i],right[len(pairs)-i-1]),key=len)
                feasible = {(e,o) for e,o in pairs[i] if any(
                    (48-e-u,48-o-w) in b for u,w in a)}
                if feasible != set(map(tuple,face["extendable"])):
                    raise ValueError("Global extendable parity counts differ")
                maximum += max(e+o for e,o in feasible)
            if maximum != cut["maximum_total"] or maximum-96 != cut["deficit_budget"]:
                raise ValueError("Deficit cap differs")
        checked += len(entire)
    return checked


def analyze(row,parent,top,folder,exe):
    prefix = row["prefix"]
    search.partner.validate_prefix(parent,prefix)
    tables = geometry(parent,prefix,row["conditioning"])
    cnf,chosen,fresh = search.encode(parent,prefix,top)
    if json.loads(json.dumps(fresh)) != row["conditioning"]:
        raise ValueError("Regenerated conditioning differs")
    status = row["status"]
    result = dict(class_id=row["class_id"],endpoint=row["endpoint"],prefix=prefix,faces=tables,status=status)
    if status == "local_exclusion":
        if not (fresh.get("pruned_prefix") or fresh.get("partition_obstruction")) or row["attempts"]:
            raise ValueError("Missing exact obstruction")
        return result
    if not row["attempts"]:
        raise ValueError("Unsolved record")
    filename = folder/"case.cnf"
    for i,step in enumerate(row["attempts"]):
        if cnf.save(filename) != step["cnf_sha256"] or cnf.count != step["variables"] or len(cnf.clauses)!=step["clauses"]:
            raise ValueError("Regenerated DIMACS differs")
        last = i == len(row["attempts"])-1
        outcome = step["outcome"]
        if outcome == "disconnected":
            if not step["cycles"] or (last and status != "unknown"):
                raise ValueError("Invalid cycle refinement")
            for c in step["cycles"]:
                cnf.clauses.append(search.audit.cycle_cut(c,chosen,set()))
        elif last and outcome == "UNSAT" and status == "solver_exclusion":
            entry = dict(**step, absolute_proof=str((search.HERE/step["proof"]).resolve()))
            proof = search.audit.replay_proof(entry,"absolute_proof",filename,exe)
            proof["proof"] = step["proof"]
            result["proof"] = proof
            result["status"] = "checked_exclusion" if proof["accepted"] else "rejected"
        elif last and outcome == "witness" and status == "witness":
            p = row["partner"]
            search.partner.verify(p,8)
            search.partner.verify(row["q9_path"],9)
            if len(p)!=96 or p[:len(prefix)]!=prefix or row["q9_path"]!=parent[::-1]+[v+256 for v in p]:
                raise ValueError("Incorrect Q9 witness")
        elif not (last and outcome == "timeout" and status == "unknown"):
            raise ValueError("Unexpected certificate state")
    return result


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("ledger",nargs="?",type=Path,default=search.HERE/"conditioned.json")
    args=cli.parse_args()
    data=json.loads(args.ledger.read_bytes())
    if data["pins"]["conditioned.py"]!=search.partner.digest(search.HERE/"conditioned.py"):
        raise ValueError("Conditioner source differs")
    output=args.ledger.with_name(args.ledger.stem+"-replay.json")
    reports=[]
    arms=search.partner.parent_arms()
    sources={p.name:search.partner.digest(p) for p in [Path(__file__),search.audit.CHECKER,search.audit.COMPILER]}
    with TemporaryDirectory(prefix="conditioned-replay-") as tmp:
        folder=Path(tmp)
        exe=folder/"VerifyLrat.exe"
        subprocess.run([str(search.audit.COMPILER),"/nologo","/optimize+","/out:"+str(exe),
                        str(search.audit.CHECKER)],check=True,capture_output=True,timeout=60)
        for row in data["records"]:
            p=search.partner.rooted_parent(arms[row["class_id"]],row["endpoint"])
            reports.append(analyze(row,p,data["settings"]["partitions"],folder,exe))
            print(row["class_id"],row["endpoint"],row["prefix"],reports[-1]["status"],flush=True)
    lookup={(r["class_id"],r["endpoint"],tuple(r["prefix"])):r["status"] for r in reports}
    def coverage(i,e,p,arm):
        state=lookup.get((i,e,p),"unqueried")
        if state in ("checked_exclusion","local_exclusion"):
            return True
        if state!="unknown":
            return False
        return all(coverage(i,e,p+(v,),arm) for v in search.partner.next_vertices(arm,p))
    covered=[]
    for i,e,p in search.open_cases():
        arm=search.partner.rooted_parent(arms[i],e)
        covered.append(dict(class_id=i,endpoint=e,prefix=p,excluded=coverage(i,e,p,arm)))
    search.save(output,dict(ledger_sha256=search.partner.digest(args.ledger),sources=sources,records=reports,
                            prior_unresolved_prefixes=covered,counts=Counter(r["status"] for r in reports)))
    if any(r["status"]=="rejected" for r in reports):
        raise RuntimeError("LRAT rejection")
    print("Covered",sum(r["excluded"] for r in covered),"of",len(covered),"previously unresolved first steps")


if __name__=="__main__":
    main()
