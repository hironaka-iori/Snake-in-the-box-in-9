"""Rebuild the opposite-end exclusions used for each reported interval."""
import gzip
from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from opposite import encode, witness
from survey import HERE, partner, save_json


def main():
    ledger=HERE/"opposite.json"
    data=json.loads(ledger.read_bytes())
    prior=json.loads((HERE/"endpoint94.json").read_bytes())
    arms=partner.parent_arms()
    summary=[]
    with TemporaryDirectory(prefix="snake248-end-audit-") as tmp:
        formula=Path(tmp)/"case.cnf"
        for row in data["records"]:
            i=row["class_id"]
            arm=partner.rooted_parent(arms[i],1)
            initial=next(r for r in prior["records"] if r["case"]==[i,1])
            if initial["status"]!="verified_exclusion" or not any(q.get("cnf_sha256")==row["inherited_94_cnf"] for q in initial["queries"]):
                raise ValueError("No matching 94-edge upper exclusion")
            reported=row["lower_witness"]
            if witness(arm,reported["partner"],row["lower"])!=reported:
                raise ValueError("Lower witness changed")
            all_firsts={(0,s) for s in partner.next_vertices(arm,[0])}
            closed={}
            for nstr,queries in row["length_queries"].items():
                n=int(nstr)
                checked=set()
                for q in queries:
                    prefix=tuple(q["prefix"])
                    if q["status"]=="witness":
                        w=witness(arm,q["partner"],n)
                        if q["joined"]!=w["joined"] or q["partner"][:len(prefix)]!=list(prefix):
                            raise ValueError("Recorded positive query failed")
                    if q["status"]!="verified_exclusion":
                        continue
                    cnf,_=encode(arm,n,prefix,q["cycles"])
                    if cnf.save(formula)!=q["cnf_sha256"]:
                        raise ValueError("Opposite-end CNF differs")
                    proof=HERE/q["proof"]
                    h=sha256()
                    with gzip.open(proof,"rb") as stream:
                        for chunk in iter(lambda:stream.read(131072),b""):
                            h.update(chunk)
                    if (h.hexdigest()!=q["raw_sha256"] or partner.digest(proof)!=q["gzip_sha256"]
                            or not q["checker"].startswith("VERIFIED UNSAT ")):
                        raise ValueError("Opposite-end proof receipt mismatch")
                    checked.add(prefix)
                if (0,) in checked or all_firsts<=checked:
                    closed[n]=sorted(checked)
            upper=min([93]+[n-1 for n in closed])
            if upper!=row["upper"] or (row["status"]=="exact")!=(upper==row["lower"]):
                raise ValueError("Incorrect combination of upper and lower bounds")
            summary.append(dict(class_id=i,lower=row["lower"],upper=upper,complete_exclusions=closed))
    save_json(HERE/"opposite-audit.json",dict(input_sha256=partner.digest(ledger),classes=summary))
    print([(r["class_id"],r["lower"],r["upper"]) for r in summary])


if __name__=="__main__":
    main()
