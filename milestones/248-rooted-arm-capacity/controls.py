"""Check the 25 published joins and pin genuinely feasible targets in the 95-edge CNF."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess

from conditioned import HERE, LAST, partner, save


def main():
    comparison = partner.PREV/"comparison.json"
    inventory = partner.PREV/"arm-structure.json"
    source = json.loads(comparison.read_bytes())
    labels = json.loads(inventory.read_bytes())
    pins = json.loads((LAST/"partners.json").read_bytes())["pins"]
    for p in (comparison,inventory,LAST/"partner.py",partner.SOLVER):
        if partner.digest(p) != pins[p.name]:
            raise ValueError(("Input pin changed",p.name))
    ids = {(a,b): labels["seed_ids_by_long_row_short_column"][i][j]
           for i,a in enumerate(labels["long_class_ids"]) for j,b in enumerate(labels["short_class_ids"])}
    records = {r["seed"]:r for r in source["one_crossing_pairs"]}
    if len(ids)!=25 or set(ids.values())!=set(records) or len(records)!=25:
        raise ValueError("Incomplete 5-by-5 positive-control bank")
    checks = []
    with TemporaryDirectory(prefix="q8-partner-positive-") as tmp:
        cnf_file = Path(tmp)/"pinned.cnf"
        for (a,b),seed in sorted(ids.items()):
            long,short = records[seed]["long"],records[seed]["short"]
            if len(long)!=97 or len(short)!=95 or long[0]!=0 or short[0]!=0 or set(long)&set(short)!={0}:
                raise ValueError(("Invalid saved arm pair",seed))
            partner.verify(long,8)
            partner.verify(short,8)
            published = long[::-1]+[v+256 for v in short]
            partner.verify(published,9)
            # Test the original 95-edge target CNF: take the shorter arm as the
            # obstacle and delete the free tip of the longer arm. The 94-edge
            # obstacle and its rooted 95-edge partner form a 190-edge join.
            target = long[:-1]
            prefix = target[:2]
            cnf,chosen = partner.encode(short,prefix)
            selected = set(target)
            if sum(v.bit_count()%2 for v in selected)!=48 or len(selected)!=96:
                raise ValueError("Incorrect positive-control quotas")
            cnf.clauses.extend([lit if v in selected else -lit] for v,lit in chosen.items())
            digest = cnf.save(cnf_file)
            out = subprocess.run([str(partner.SOLVER),"-q",str(cnf_file)],capture_output=True,timeout=10)
            if out.returncode!=10 or b"s SATISFIABLE" not in out.stdout:
                raise ValueError(("Known positive-control CNF did not give SAT",seed,out.returncode))
            truth = {int(w) for line in out.stdout.splitlines() if line.startswith(b"v ")
                     for w in line.split()[1:] if int(w)>0}
            if {v for v,lit in chosen.items() if lit in truth}!=selected:
                raise ValueError(("Changed pinned positive-control membership",seed))
            partner.verify(target,8)
            partner.verify(short[::-1]+[v+256 for v in target],9)
            checks.append(dict(bank_seed=seed,long_class=a,short_class=b,
                               long_q8_pairs=4656,short_q8_pairs=4465,published_191_q9_pairs=18336,
                               target_95_q8_pairs=4560,alternate_190_q9_pairs=18145,
                               pinned_prefix=prefix,positive_cnf_sha256=digest,pinned_sat=True))
    result = dict(inputs={p.name:partner.digest(p) for p in
                  (Path(__file__),comparison,inventory,LAST/"partner.py",partner.SOLVER)},
                  evidence="Published 96+94 joins establish attainment for each 96-arm class at its documented joining endpoint. Swapped 94+95 instances independently exercise the 95-edge solver encoding.",
                  checks=checks)
    save(HERE/"controls.json",result)
    print("Verified all",len(checks),"published 191-edge joins and pinned 95-edge partner controls")


if __name__=="__main__":
    main()
