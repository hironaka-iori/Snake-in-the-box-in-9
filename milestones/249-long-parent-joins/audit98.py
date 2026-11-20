"""Check the full 98-edge parent, inherited exclusions and new partner-length cover."""
from collections import defaultdict
import gzip
from pathlib import Path
import re
from tempfile import TemporaryDirectory

import audit
from audit import HERE, OLD, SOURCE, file_hash, path_ok, read, require, verified_partner
import joins


def open_prefixes(parent, length, queries):
    excluded = {tuple(r["prefix"]) for r in queries if r["status"] == "excluded"}
    attempted = {tuple(r["prefix"]) for r in queries}
    todo, pending = [(0,)], []
    while todo:
        p = todo.pop()
        if p in excluded:
            continue
        if p not in attempted or len(p) == length + 1:
            pending.append(p)
            continue
        for axis in range(8):
            v = p[-1] ^ (1 << axis)
            if v not in parent and v not in p and all((w ^ v).bit_count() > 1 for w in p[:-1]):
                todo.append(p + (v,))
    return sorted(pending, key=lambda p: (len(p),p))


def check_full(parent, row, formula, archives):
    n, p = row["length"], row["prefix"]
    require(1 <= n <= 91 and 1 <= len(p) <= n + 1 and p[0] == 0
            and set(p) & set(parent) == {0}, "Invalid query prefix")
    path_ok(p,8)
    cnf, chosen = joins.opposite.encode(parent,n,p)
    require(set(chosen) == (set(range(256)) - set(parent[1:])), "Wrong full-parent domain")
    cycles = []
    status = row["status"]
    require(status in {"excluded","witness","open"} and (row["attempts"] or status=="open"),
            "Incomplete query status")
    for i, step in enumerate(row["attempts"]):
        key = cnf.save(formula)
        require(step["cnf_sha256"] == key, "Intermediate full-parent formula differs")
        last = i == len(row["attempts"]) - 1
        outcome = step["outcome"]
        if outcome == "disconnected":
            require(step["cycles"] and (not last or status=="open"), "Missing cycle cut")
            for c in step["cycles"]:
                cnf.clauses.append(audit.check_cycle(c,chosen))
                cycles.append(c)
        elif last and outcome == "verified_unsat" and status == "excluded":
            proof = "direct98-proofs/" + key + ".lrat.gz"
            require(key == row["cnf_sha256"] and proof == row["proof"], "Direct LRAT binding")
            m = re.fullmatch(r"VERIFIED UNSAT variables=(\d+) input_clauses=(\d+) additions=(\d+) "
                             r"deleted_clauses=(\d+) hints=(\d+) empty_id=(\d+)", row["checker"])
            require(m and int(m[1])==cnf.count and int(m[2])==len(cnf.clauses) and int(m[3])>0
                    and int(m[6])>len(cnf.clauses), "Unmatched checker receipt")
            if proof not in archives:
                archives[proof] = file_hash(HERE/proof),file_hash(HERE/proof,gzip.open)
            require(archives[proof] == (row["gzip_sha256"],row["raw_sha256"]), "Full proof hashes")
        elif last and outcome == "connected" and status == "witness":
            verified_partner(parent,row,n)
            require(row["partner"][:len(p)] == p, "Incorrect positive prefix")
        else:
            require(last and outcome=="timeout" and status=="open","Unexpected final state")
    require(cycles==row["cycles"],"Full-parent cycle history")


def main():
    direct = read(HERE/"direct98.json")
    prior = read(HERE/"audit.json")
    require(prior["source_sha256"] == file_hash(HERE/"audit.py"),"Previous audit source changed")
    source_files = [HERE/"direct98.py",joins.INVENTORY,SOURCE/"donors.json",HERE/"joins.py",
                    OLD/"opposite.py",OLD/"certify.py",Path(joins.partner.__file__),SOURCE/"free_outer.py",
                    joins.partner.SOURCE/"arc_sat.py",joins.CHECKER,joins.COMPILER,joins.partner.SOLVER]
    require(direct["pins"] == {p.name:file_hash(p) for p in source_files}, "Direct search inputs differ")
    require(re.fullmatch("[0-9a-f]{64}",direct["checker_executable_sha256"]),"Missing checker identity")
    inventory = read(joins.INVENTORY)
    bank = read(SOURCE/"donors.json")["shapes"]
    examples = read(SOURCE/"comparison.json")
    inner_file = HERE/"partners-92.json"
    inner = read(inner_file)
    for p in (inner_file,joins.INVENTORY,SOURCE/"donors.json",SOURCE/"comparison.json"):
        require(file_hash(p)==prior["inputs"][p.relative_to(HERE.parents[1]).as_posix()],
                ("Previous audit input changed",p.name))
    full = bank[20]["path"]
    require(full==examples["examples"]["optimal_98"]["path"] and
            [r["path"] for r in inventory["rows"] if r["edges"]==98 and r["donor_index"]==20] == [full]
            and len(full)==99 and [full[0],full[-1]]==[0,78],"Wrong archived 98-edge path")
    path_ok(full,8)
    require(set(direct["inherited"])==set(direct["roots"])==set(direct["summary"])==
            set(direct["witnesses"])=={"0","78"} and all(q["root"] in {0,78} for q in direct["records"]),
            "Root coverage")
    files, full_files, result = {}, {}, []
    with TemporaryDirectory(prefix="snake249-audit98-") as tmp:
        formula = Path(tmp)/"reconstructed.cnf"
        for end,(root,sub_id,sub_end) in enumerate(((0,15,0),(78,17,1))):
            key = str(root)
            parent = audit.rooted(full,end)
            small = audit.rooted(bank[sub_id]["path"],sub_end)
            require(parent==direct["roots"][key] and parent[:97]==small and len(small)==97,
                    "Rooted subpath does not reconstruct")
            rec = next(r for r in inner["records"] if (r["donor"],r["endpoint"],r["prefix"],r["status"])==
                       (sub_id,sub_end,[0],"excluded"))
            audit.row_check(rec,small,92,formula,files)
            source = direct["inherited"][key]
            require(source==dict(length_excluded=92,donor=sub_id,endpoint=sub_end,
                                 deleted_free_end_vertices=parent[97:],cnf_sha256=rec["cnf_sha256"],
                                 proof=rec["proof"],gzip_sha256=rec["gzip_sha256"],checker=rec["checker"]),
                    "Inherited proof disagrees with the subarm archive")
            old = next(c for c in prior["cases"] if (c["donor"],c["endpoint"])==(20,end))
            require(old["upper"]<=91 and any(t["source"]==[sub_id,sub_end] and t["upper"]<=91
                    for t in old["transfers"]),"Previous audit lacks 92-edge exclusion")
            positive = direct["witnesses"][key]
            lower = positive["partner_edges"]
            verified_partner(parent,positive,lower)
            require(len(parent)+lower == positive["joined_edges"],"Wrong lift length")
            group = defaultdict(list)
            for row in direct["records"]:
                if row["root"] != root:
                    continue
                check_full(parent,row,formula,full_files)
                if row["status"]=="witness":
                    require(row["length"]<=lower,"Saved best misses a verified witness")
                group[row["length"]].append(row)
            upper = 91
            levels, pending = [], []
            while upper > lower:
                pending = open_prefixes(parent,upper,group[upper])
                levels.append(dict(length=upper,records=len(group[upper]),open_prefixes=pending))
                if pending:
                    break
                upper -= 1
            require(lower<=upper,"Full-parent witness contradicts exclusion")
            if group.get(lower) and not open_prefixes(parent,lower,group[lower]):
                raise ValueError("A complete exclusion conflicts with the lower witness")
            claimed = dict(lower=lower,upper=upper,exact=lower==upper,
                           open_prefixes=[list(p) for p in pending] if upper>lower else [])
            require(claimed==direct["summary"][key],"Reconstructed boundary or outstanding leaves differ")
            result.append(dict(root=root,source_at_92=[sub_id,sub_end],partner=claimed,
                               joined_lower=99+lower,joined_upper=99+upper,levels=levels))
            print("root",root,"partner",lower,upper,"joined",99+lower,99+upper,flush=True)
    joins.save_json(HERE/"audit98.json",dict(source_sha256=file_hash(Path(__file__)),
        inputs=audit.INPUTS,cases=result,inherited_proofs=len(files),direct_proofs=len(full_files),
        checked_queries=len(direct["records"]),checker_executable_sha256=direct["checker_executable_sha256"],
        scope="Reconstructed full-parent formulas, both archive digests, recorded LRAT replay results, "
              "all witness adjacencies and exhaustive rooted prefix coverage."))


if __name__=="__main__":
    main()
