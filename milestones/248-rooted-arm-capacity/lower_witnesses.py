"""Seek high connected witnesses in any remaining opposite-end intervals."""
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from time import monotonic

from opposite import encode, extract, witness
from survey import HERE, partner, save_json


def main():
    source=HERE/"opposite.json"
    data=json.loads(source.read_bytes())
    dest=HERE/"lower-witnesses.json"
    arms=partner.parent_arms()
    record=dict(input_sha256=partner.digest(source),records=[])
    with TemporaryDirectory(prefix="snake248-feasible-") as tmp:
        formula=Path(tmp)/"case.cnf"
        for row in data["records"]:
            if row["status"]=="exact":
                continue
            i=row["class_id"]
            parent=partner.rooted_parent(arms[i],1)
            low=row["lower_witness"]
            result=dict(class_id=i,upper=row["upper"],lower_witness=low,queries=[])
            record["records"].append(result)
            for n in range(row["upper"],max(row["lower"],row["upper"]-5),-1):
                # Length n is exact. Period five excludes disconnected cycles
                # of length not divisible by five; any path can use its indices mod five.
                cnf,chosen=encode(parent,n)
                cells={v:[cnf.variable() for _ in range(5)] for v in chosen}
                for v,colors in cells.items():
                    cnf.clauses.append([-chosen[v],*colors])
                    for j,c in enumerate(colors):
                        cnf.clauses.append([-c,chosen[v]])
                        cnf.clauses.extend([-c,-other] for other in colors[j+1:])
                    for w in partner.NEIGHBOURS[v]:
                        if w not in chosen or w<=v:
                            continue
                        for j,c in enumerate(colors):
                            for k in (j,(j+2)%5,(j+3)%5):
                                cnf.clauses.append([-c,-cells[w][k]])
                    ns=[cells[w] for w in partner.NEIGHBOURS[v] if w in chosen]
                    # All selected vertices except the initial vertex have a predecessor.
                    for j,c in enumerate(colors):
                        if v:
                            cnf.clauses.append([-c]+[g[(j-1)%5] for g in ns])
                        if v==0 or j!=n%5 or (v.bit_count()-n)%2:
                            cnf.clauses.append([-c]+[g[(j+1)%5] for g in ns])
                cnf.clauses.append([cells[0][0]])
                for j in range(5):
                    for p in range(2):
                        quota=sum(t%5==j and t%2==p for t in range(n+1))
                        cnf.exactly([group[j] for v,group in cells.items() if v.bit_count()%2==p],quota)
                until=monotonic()+5
                result["queries"].append(n)
                found=None
                while monotonic()<until:
                    cnf.save(formula)
                    try:
                        ans=subprocess.run([str(partner.SOLVER),"-q","--seed=7",str(formula)],
                                           capture_output=True,timeout=max(.05,until-monotonic()))
                    except subprocess.TimeoutExpired:
                        break
                    if ans.returncode==20:
                        break
                    if ans.returncode!=10:
                        raise RuntimeError(ans.stderr[-200:])
                    lits={int(v) for l in ans.stdout.splitlines() if l.startswith(b"v ") for v in l.split()[1:] if int(v)>0}
                    found,cycles=extract(parent,n,[0],{v for v,lit in chosen.items() if lit in lits})
                    if found:
                        result["lower_witness"]=witness(parent,found["partner"],n)
                        break
                    cnf.clauses.extend(partner.cycle_clause(chosen,c) for c in cycles)
                save_json(dest,record)
                if found:
                    break
            print(i,result["lower_witness"]["partner_edges"],row["upper"],flush=True)
    save_json(dest,record)


if __name__=="__main__":
    main()
