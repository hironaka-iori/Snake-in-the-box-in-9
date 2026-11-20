"""Construct rooted partners by donor transport, feasible SAT models and local path edits."""
from argparse import ArgumentParser
import csv
from hashlib import sha256
import json
from pathlib import Path
from random import Random
import subprocess
from tempfile import TemporaryDirectory
from time import monotonic
import zipfile

from joins import HERE, LAST, INVENTORY, encode, inputs, opposite, partner, save_json


def archived_arms(donors, expected_hash):
    archive = HERE.parents[1] / "work" / "record_snakes.csv.zip"
    with zipfile.ZipFile(archive) as source:
        raw = source.read("snakes_dim9_190.csv")
    if sha256(raw).hexdigest() != expected_hash:
        raise ValueError("The 190-edge source changed")
    rows = list(csv.DictReader(raw.decode("utf-8").splitlines()))
    saved = {}
    for idx in (99, 114):
        _, row, axis, start, offset = donors[idx]["origin"]
        path = list(map(int, rows[row]["vertices"].split()))
        partner.verify(path, 9)
        def project(v):
            return (v & ((1 << axis)-1)) | ((v >> (axis+1)) << axis)
        left = start+offset
        right = left+len(donors[idx]["path"])-1
        if [project(v) for v in path[left:right+1]] != donors[idx]["path"]:
            raise ValueError("Published segment does not reproduce the donor")
        for end, j, direction in ((0,left,-1),(1,right,1)):
            k = j+direction
            if not 0 <= k < len(path) or path[j]^path[k] != 1<<axis:
                continue
            arm = [0]
            while 0 <= k+direction < len(path) and path[k]^path[k+direction] != 1<<axis:
                k += direction
                arm.append(project(path[k])^project(path[j]))
            saved[idx,end] = (arm, dict(source="published 190-edge path",row=row,axis=axis))
    return saved


def component_path(selected):
    path = [0]
    seen = {0}
    while True:
        rest = selected.intersection(partner.NEIGHBOURS[path[-1]])-seen
        if not rest:
            return path
        if len(rest) != 1:
            raise ValueError("The selected root component branches")
        v = rest.pop()
        path.append(v)
        seen.add(v)


def sat_paths(parent, length, seconds, folder, seed, record, accept):
    cnf, chosen = encode(parent, length, [0], [])
    model = folder / "positive.cnf"
    until = monotonic()+seconds
    while monotonic()<until:
        key = cnf.save(model)
        try:
            trial = subprocess.run([str(partner.SOLVER), "-q", "--seed="+str(seed), str(model)],
                                   capture_output=True, timeout=max(.01, until-monotonic()))
        except subprocess.TimeoutExpired:
            record.append(dict(length=length,cnf=key,outcome="timeout"))
            break
        if trial.returncode==20:
            record.append(dict(length=length,cnf=key,outcome="native_unsat_without_replay"))
            break
        if trial.returncode!=10 or b"s SATISFIABLE" not in trial.stdout:
            raise RuntimeError(trial.stderr[-400:])
        truth = {int(v) for line in trial.stdout.splitlines() if line.startswith(b"v ")
                 for v in line.split()[1:] if int(v)>0}
        selected = {v for v,k in chosen.items() if k in truth}
        found, cycles = opposite.extract(parent,length,[0],selected)
        path = found["partner"] if found else component_path(selected)
        record.append(dict(length=length,cnf=key,outcome="model",root_component_edges=len(path)-1,
                           cycle_lengths=list(map(len,cycles))))
        accept(path,dict(source="root component of a SAT model",cnf=key,target=length))
        if found:
            break
        for cycle in cycles:
            cnf.clauses.append(partner.cycle_clause(chosen,cycle))


def local_search(parent, best, seconds, seed, accept):
    """Lift a subpath across an unused coordinate, swap a corner, or regrow a suffix."""
    rng = Random(seed)
    until = monotonic()+seconds
    forbidden = set(parent[1:])
    current = best[:]
    if len(current)==1:
        moves = sorted(set(partner.NEIGHBOURS[0])-forbidden)
        if not moves:
            return 0
        current.append(moves[0])
        best = current[:]
        accept(best,dict(source="legal first step"))
    restarts = 0
    while monotonic()<until and len(best)<96:
        restarts += 1
        if len(current)<4 or rng.randrange(5)==0:
            current = best[:]
        occupied = set(current)
        a = rng.randrange(len(current)-1)
        b = min(len(current)-1,a+rng.randint(2,14))
        if b-a >= 2 and rng.randrange(2)==0:
            # Replace the arc from a to b by the same arc in a parallel face.
            bit = 1<<rng.randrange(8)
            window = current[a:b+1]
            lifted = [v^bit for v in window]
            survivors = (occupied-set(window[1:-1]))
            if not (set(lifted) & (survivors | forbidden)):
                outside = survivors-{current[a],current[b]}
                if not any(outside.intersection(partner.NEIGHBOURS[v]) for v in lifted):
                    chord = any(v in partner.NEIGHBOURS[current[a]] for v in lifted[1:]) or any(
                                v in partner.NEIGHBOURS[current[b]] for v in lifted[:-1])
                    if not chord:
                        current = current[:a+1]+lifted+current[b:]
        elif a+2<len(current) and rng.randrange(2)==0:
            replacement = current[a]^current[a+1]^current[a+2]
            if replacement not in occupied|forbidden and (occupied.intersection(
                    partner.NEIGHBOURS[replacement]) == {current[a],current[a+2]}):
                current[a+1] = replacement
        else:
            cut = max(1,len(current)-rng.randint(0,min(20,len(current)-1)))
            ext = current[:cut]
            allowed = set(range(256))-forbidden-set(ext)
            for v in ext[:-1]:
                allowed.difference_update(partner.NEIGHBOURS[v])
            while True:
                moves = allowed.intersection(partner.NEIGHBOURS[ext[-1]])
                if not moves:
                    break
                allowed.difference_update(partner.NEIGHBOURS[ext[-1]])
                # Prefer a continuation with a small positive count of onward moves.
                v = min(moves,key=lambda q:(len(allowed.intersection(partner.NEIGHBOURS[q])) or 10)
                        +rng.random()*3)
                ext.append(v)
            if len(ext)+rng.randint(0,5)>=len(current):
                current = ext
        if len(current)>len(best):
            best = current[:]
            accept(best,dict(source="local rerouting or suffix regrowth",seed=seed,iteration=restarts))
    return restarts


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--ids",type=int,nargs="+")
    cli.add_argument("--seed",type=int,default=1)
    cli.add_argument("--seconds",type=float,default=9,help="Search budget per oriented parent")
    opts = cli.parse_args()
    parents = inputs()
    if opts.seconds<=0 or (opts.ids and set(opts.ids)-{i for i,_ in parents}):
        cli.error("Invalid donor or per-endpoint budget")
    donor_file = partner.PREV/"donors.json"
    bank = json.loads(donor_file.read_bytes())
    seeds = archived_arms(bank["shapes"],bank["parent_member_sha256"])
    pins = {p.name:partner.digest(p) for p in (Path(__file__),HERE/"joins.py",INVENTORY,donor_file,
            LAST/"opposite.py",LAST/"endpoint94.py",Path(partner.__file__),partner.SOLVER)}
    dest = HERE/"witnesses.json"
    result = json.loads(dest.read_bytes()) if dest.exists() else dict(pins=pins,records=[])
    if result["pins"]!=pins:
        raise ValueError("Witness checkpoint sources differ")
    with TemporaryDirectory(prefix="q8-rooted-witnesses-") as temp:
        for (idx,end),parent in parents.items():
            if opts.ids and idx not in opts.ids:
                continue
            row = next((r for r in result["records"] if r["case"]==[idx,end]),None)
            if row is None:
                row = dict(case=[idx,end],parent=parent,receipts=[],runs=[])
                result["records"].append(row)
            if row["parent"]!=parent:
                raise ValueError("Oriented parent changed")
            if "best" in row and row["best"]!=opposite.witness(parent,row["best"]["partner"],row["best"]["partner_edges"]):
                raise ValueError("Stored witness differs from direct reconstruction")
            def accept(path,source):
                if "best" not in row or len(path)>len(row["best"]["partner"]):
                    row["best"] = opposite.witness(parent,path,len(path)-1)
                    row["receipts"].append(dict(partner_edges=len(path)-1,**source))
                    save_json(dest,result)
            if any(r.get("completed") and r["seed"]==opts.seed and r["seconds"]==opts.seconds for r in row["runs"]):
                continue
            run = dict(seed=opts.seed,seconds=opts.seconds,queries=[])
            row["runs"].append(run)
            until = monotonic()+opts.seconds
            accept([0],dict(source="root"))
            if (idx,end) in seeds:
                accept(*seeds[idx,end])
            transported, receipt = opposite.donor_bound(parent,bank["shapes"],min(.75,opts.seconds/7))
            accept(transported,dict(source="transported donor prefix",details=receipt))
            trial_seed = opts.seed+2*idx+end
            run["initial_reroutes"] = local_search(parent,row["best"]["partner"],min(.35,opts.seconds/12),
                                                      trial_seed,accept)
            # Search looser cardinalities early enough to supply long connected seeds.
            for length in (88,90,92,93,94,95):
                budget = until-monotonic()
                if budget<=.25 or row["best"]["partner_edges"]>=95:
                    break
                if length<=row["best"]["partner_edges"]:
                    continue
                sat_paths(parent,length,min(budget-.15,max(.20,opts.seconds/5)),Path(temp),
                          trial_seed,run["queries"],accept)
            run["final_reroutes"] = local_search(parent,row["best"]["partner"],max(0,until-monotonic()),
                                                   trial_seed+1,accept)
            run["completed"] = True
            save_json(dest,result)
            print(idx,end,row["best"]["partner_edges"],"partner edges",flush=True)
            if row["best"]["joined_edges"]>=192:
                return


if __name__=="__main__":
    main()
