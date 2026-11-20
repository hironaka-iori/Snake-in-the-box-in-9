"""Find explicit lower witnesses for the 98-edge parent while its upper search is partial."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess

from direct98 import HERE, opposite, partner, rooted_data, save_json, summary, witness
from witnesses import component_path


def main():
    dest = HERE/"direct98.json"
    data = json.loads(dest.read_bytes())
    journal = HERE/"positive98.json"
    output = dict(script_sha256=partner.digest(Path(__file__)), cases=[])
    with TemporaryDirectory(prefix="snake249-positive-") as directory:
        temp = Path(directory)
        parents, inherited = rooted_data(temp)
        if inherited != data["inherited"]:
            raise ValueError("Changed upper-bound evidence")
        for root,parent in parents.items():
            key = str(root)
            initial = data["witnesses"][key]["partner"]
            upper = summary(parent,root,data)["upper"]
            row = dict(root=root, upper_before=upper, attempts=[])
            output["cases"].append(row)
            def accept(path):
                if len(path)>len(data["witnesses"][key]["partner"]):
                    hit = witness(parent,path)
                    if hit["partner_edges"]>upper:
                        raise ValueError("Positive path contradicts the saved ceiling")
                    data["witnesses"][key] = hit
                    data["summary"][key] = summary(parent,root,data)
                    save_json(dest,data)
            greedy,_ = opposite.improve_seed(parent,initial,0.8,249+root)
            accept(greedy)
            # Seek a long feasible model first, then close the gap closest to the upper bound.
            for n in dict.fromkeys([upper-3,upper-2,upper-1,upper,upper-4,upper-6,upper-9]):
                if n<=data["witnesses"][key]["partner_edges"]:
                    continue
                cnf,chosen = opposite.encode(parent,n,[0])
                for step in range(3):
                    path = temp/"positive.cnf"
                    digest = cnf.save(path)
                    rec = dict(length=n, refinement=step, cnf_sha256=digest)
                    row["attempts"].append(rec)
                    try:
                        result = subprocess.run([str(partner.SOLVER),"-q","--seed=3",str(path)],
                                                capture_output=True,timeout=2.5)
                    except subprocess.TimeoutExpired:
                        rec["status"]="open"
                        break
                    if result.returncode==20 and b"s UNSATISFIABLE" in result.stdout:
                        rec["status"]="no_model_in_probe"
                        break
                    if result.returncode!=10 or b"s SATISFIABLE" not in result.stdout:
                        raise RuntimeError(result.stderr[-300:])
                    truth = {int(t) for line in result.stdout.splitlines() if line.startswith(b"v ")
                             for t in line.split()[1:] if int(t)>0}
                    selected = {v for v,lit in chosen.items() if lit in truth}
                    found,cycles = opposite.extract(parent[:97],n,[0],selected)
                    arm = found["partner"] if found else component_path(selected)
                    accept(arm)
                    rec.update(status="model", component_edges=len(arm)-1,cycles=cycles)
                    if found:
                        break
                    cnf.clauses.extend(partner.cycle_clause(chosen,c) for c in cycles)
            row["witness"]=data["witnesses"][key]
            save_json(journal,output)
            print("root",root,"verified lower",row["witness"]["partner_edges"],"upper",upper,flush=True)


if __name__=="__main__":
    main()
