"""Separate the remaining fixed-middle crossing cases by arm lengths and vertex parity."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import json
import subprocess
from free_outer import HERE, SOLVER, encode, extract


def forbid_short_cycles(cnf, chosen, fixed):
    available=set(chosen)|fixed
    added=set()
    for dim in (2,3):
        for axes in combinations([1<<i for i in range(9)],dim):
            offsets=[0]
            for axis in axes:
                offsets += [v^axis for v in offsets]
            full=sum(axes)
            for root in available:
                if root&full:
                    continue
                for omit in ([None] if dim==2 else offsets[:4]):
                    cycle=[root^v for v in offsets if omit is None or (v!=omit and v!=(omit^full))]
                    if all(v in available for v in cycle):
                        clause=tuple(sorted(-chosen[v] for v in cycle if v in chosen))
                        added.add(clause)
    cnf.clauses.extend(list(c) for c in sorted(added))
    return len(added)


def decide(middles,q,first_length,file,seconds):
    cnf,chosen,fixed=encode(middles,q)
    for x,length in enumerate((first_length,191-first_length)):
        outer_count=length-47
        for parity in (0,1):
            # The 48 vertices of the upper middle split evenly by colour.
            count=outer_count//2+int(outer_count%2==1 and parity==q.bit_count()%2)
            def in_group(v):
                return (v&128)==0 and v>>8==x and (v&127).bit_count()%2==parity
            count-=sum(in_group(v) for v in fixed)
            cnf.exactly([lit for v,lit in chosen.items() if in_group(v)],count)
    added=forbid_short_cycles(cnf,chosen,fixed)
    attempts=[]
    remaining=seconds
    status="unknown"
    path=None
    while remaining>0:
        entry=dict(cnf_sha256=cnf.save(file),clauses=len(cnf.clauses))
        attempts.append(entry)
        start=monotonic()
        try:
            p=subprocess.run([str(SOLVER),"-q",str(file)],capture_output=True,timeout=remaining)
        except subprocess.TimeoutExpired:
            entry["result"]="timeout"
            break
        remaining-=monotonic()-start
        if p.returncode==20 and b"s UNSATISFIABLE" in p.stdout:
            status=entry["result"]="native_exclusion"
            break
        if p.returncode!=10 or b"s SATISFIABLE" not in p.stdout:
            raise RuntimeError((p.returncode,p.stderr[:200]))
        positive={int(s) for line in p.stdout.splitlines() if line.startswith(b"v ") for s in line.split()[1:] if int(s)>0}
        selected=fixed|{v for v,i in chosen.items() if i in positive}
        path,cycles=extract(selected,middles,q)
        if path is not None:
            if sum(v<256 for v in path)!=first_length+1:
                raise ValueError("Arm length mismatch")
            status=entry["result"]="witness"
            break
        entry.update(result="disconnected",cycles=cycles)
        cnf.clauses.extend([-chosen[v] for v in cycle if v in chosen] for cycle in cycles)
    return dict(q=q,first_length=first_length,second_length=191-first_length,
                short_cycle_clauses=added,status=status,attempts=attempts,path=path)


def main():
    source=HERE/"free-outer.json"
    data=json.loads(source.read_bytes())
    cases=[]
    with TemporaryDirectory(prefix="q9-246-outer-") as folder:
        for row in data["rows"]:
            if row["status"]!="unknown":
                continue
            for length in range(93,99):
                case=decide(data["middles"],row["q"],length,Path(folder)/"model.cnf",1.5)
                cases.append(case)
                if case["path"]:
                    break
            if cases[-1]["path"]:
                break
    result=dict(input_sha256=sha256(source.read_bytes()).hexdigest(),solver_sha256=sha256(SOLVER.read_bytes()).hexdigest(),
                seconds_per_case=1.5,records=cases,outcomes=Counter(r["status"] for r in cases))
    (HERE/"outer-refinement.json").write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print(result["outcomes"])
    print("remaining",[(r["q"],r["first_length"]) for r in cases if r["status"]=="unknown"])


if __name__=="__main__":
    main()
