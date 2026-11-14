"""Independent word-assignment solver for a frozen lower-dimensional parent region."""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import tempfile
import gzip
import shutil
import subprocess
from pysat.solvers import Cadical195
from probe_comparison import validate
from solve import save

PIN="cfa2e8ed386259be99cd2564361591cd92a3b7bc"
MILESTONES={9:"209-slice-capacity",24:"209-slice-capacity",23:"211-subset-capacity",22:"216-joint-word-support"}


def bits(mask):
    while mask:
        bit=mask&-mask;mask^=bit
        yield bit.bit_length()-1


def region(case,index,budget,solver_name,checker=None,baseline=False,generated=False):
    milestone=MILESTONES.get(case,"216-joint-word-support")
    prefix=PIN+":milestones/"+milestone+f"/data/case-{case}/"
    def get(name):
        return subprocess.check_output(["git","show",prefix+name])
    if generated:
        assert baseline
        from parent_family import construct
        m,perms=construct(case)
        mm=json.dumps(m,sort_keys=True,separators=(",",":")).encode()
        sr=b""
    else:
        sr=get("state.json");state=json.loads(sr)
        mm=get("model.json");pp=get("permutations.json")
        assert sha256(mm).hexdigest()==state["model_pins"]["model.json"]
        assert sha256(pp).hexdigest()==state["model_pins"]["permutations.json"]
        m=json.loads(mm);perms=json.loads(pp)
    ds=(m["domains"] if baseline else next(r for r in state["frontier"] if r["id"]==index)["domains"])
    for root,old in zip(ds,m["domains"]):assert root and root&~old==0
    n=len(ds)
    def lit(i,a):return 1+64*i+a
    def emit(solver):
        for i,d in enumerate(ds):
            ls=[lit(i,a) for a in bits(d)]
            solver.add_clause(ls)
            for u,v in combinations(ls,2):solver.add_clause([-u,-v])
        if solver_name=="cadical195_rows":
            # Every bit direction is symmetric before its first occurrence.
            # In canonical chronological order, all bits previously used form
            # an initial segment. A used bit first appears as a 1 in a word.
            for i,d in enumerate(ds):
                for b in range(6):
                    f=1+n*(64+len(perms))+6*i+b
                    earlier=[f-6] if i else []
                    ones=[lit(i,w) for w in bits(d) if w>>b&1]
                    solver.add_clause([-f,*earlier,*ones])
                    for x in earlier+ones:solver.add_clause([-x,f])
                    if i and b:solver.add_clause([-f,f-7])
        for c in m["constraints"]:
            i,j=c["x"],c["y"]
            cols={b:[] for b in bits(ds[j])}
            for a in bits(ds[i]):
                good=ds[j]&c["rows"][a]
                for b in bits(good):cols[b].append(a)
                if good==ds[j]:continue
                if good.bit_count()*2>ds[j].bit_count():
                    for b in bits(ds[j]^good):solver.add_clause([-lit(i,a),-lit(j,b)])
                else:solver.add_clause([-lit(i,a)]+[lit(j,b) for b in bits(good)])
            for b,good in cols.items():
                if len(good)*2<=ds[i].bit_count():
                    solver.add_clause([-lit(j,b)]+[lit(i,a) for a in good])
        for excluded in m["nogoods"]:
            if all(d>>v&1 for d,v in zip(ds,excluded)):
                solver.add_clause([-lit(i,v) for i,v in enumerate(excluded)])
        # For permutation p, first differing position must have smaller word
        # than its image. Prefix flag means every earlier chosen word is fixed.
        for k,p in enumerate(perms):
            if all(a==b for a,b in enumerate(p)):continue
            previous=None
            for i,d in enumerate(ds):
                fixed=[a for a in bits(d) if a==p[a]]
                prefix=[] if previous is None else [-previous]
                for a in bits(d):
                    if a>p[a]:solver.add_clause(prefix+[-lit(i,a)])
                if not fixed:break
                if len(fixed)==d.bit_count():continue
                flag=1+64*n+k*n+i
                for a in fixed:solver.add_clause(prefix+[-lit(i,a),flag])
                previous=flag
    from pysat.solvers import Solver
    real_solver="cadical195" if solver_name=="cadical195_rows" else solver_name
    with Solver(name=real_solver,with_proof=checker is not None) as solver:
        clauses=[]
        if checker is None:emit(solver)
        else:
            class Capture:
                def add_clause(self,clause):
                    solver.add_clause(clause)
                    clauses.append(clause)
            emit(Capture())
        solver.conf_budget(budget)
        ans=solver.solve_limited()
        out=dict(source=PIN,milestone="generated from pinned parent" if generated else milestone,case=case,region=index,
                 state_sha256=sha256(sr).hexdigest() if sr else None,model_sha256=sha256(mm).hexdigest(),
                 solver=solver_name,budget=budget,stats=solver.accum_stats(),
                 status={False:"UNSAT",None:"OPEN",True:"SAT"}[ans])
        if ans:
            pos={l for l in solver.get_model() if l>0}
            out["solution"]=[next(a for a in bits(ds[i]) if lit(i,a) in pos) for i in range(n)]
            out["vertices"]=validate(m,perms,ds,out)
        if ans is False and checker is not None:
            from pysat.solvers import pysolvers
            prefix=Path(f"parent-proof-{case}-{index}")
            formula=prefix.with_suffix(".cnf")
            tmp=prefix.with_suffix(".bin")
            core=prefix.with_suffix(".core")
            with formula.open("w",newline="\n") as f:
                f.write(f"p cnf {max(abs(u) for c in clauses for u in c)} {len(clauses)}\n")
                for c in clauses:f.write(" ".join(map(str,c))+" 0\n")
            # Convert CaDiCaL's proof to portable ASCII for the Windows checker.
            engine=solver.solver
            pysolvers.flushpr(engine.prfp)
            engine.prfile.seek(0)
            from proof_ascii import write_ascii
            with tmp.open("wb") as f:write_ascii(engine.prfile,f)
            first=subprocess.run([str(checker),str(formula),str(tmp),"-l",str(core)],capture_output=True)
            assert first.returncode==0 and b"s VERIFIED" in first.stdout.splitlines()
            final=subprocess.run([str(checker),str(formula),str(core)],capture_output=True)
            assert final.returncode==0 and b"s VERIFIED" in final.stdout.splitlines()
            out["checker_tail"]=final.stdout.decode(errors="replace").splitlines()[-10:]
            from rerun_deep_certificate import digest
            for f in (formula,core):
                out[f.suffix[1:]+"_sha256"]=digest(f)
                with f.open("rb") as src,Path(str(f)+".gz").open("wb") as dst:
                    with gzip.GzipFile(filename="",fileobj=dst,mode="wb",mtime=0,compresslevel=5) as gz:
                        shutil.copyfileobj(src,gz)
            tmp.unlink()
    out["scope"]="full pinned model" if baseline else "saved frontier region"
    tag="checked" if checker else solver_name
    save(Path(f"parent-sat-{case}-{index}-{tag}.json"),out)
    print(case,index,solver_name,out["status"],out["stats"],flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("case",type=int);parser.add_argument("region",type=int)
    parser.add_argument("--budget",type=int,default=2000000)
    parser.add_argument("--solver",default="cadical195")
    parser.add_argument("--checker",type=Path)
    parser.add_argument("--full",action="store_true")
    parser.add_argument("--generated",action="store_true")
    a=parser.parse_args();region(a.case,a.region,a.budget,a.solver,
                                 a.checker.resolve() if a.checker else None,a.full,a.generated)
