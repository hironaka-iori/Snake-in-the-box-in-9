"""Allow both Q8 faces to vary around a known one-crossing 191-edge snake."""
import argparse
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from bank_partner import families
from solve import defects,save


def solve(seed,freedom,budget,short_first,encoding,record=None,tag=None,positive=False,checker=None,first_size=None):
    if record is None:record=families()[96][seed]
    old=[record["parent"],record["known_partner"]]
    sizes=[97,96] if short_first else [98,95]
    if first_size is not None:
        assert 94<=first_size<=99
        sizes=[first_size,193-first_size]
    if positive:sizes=[97,95]
    assert sum(sizes)==(192 if positive else 193)
    pool=IDPool();selected={};end={};caps={}
    for side,size in enumerate(sizes):
        for v in range(256):selected[side,v]=pool.id(("v",side,v))
        for v in range(1,256):
            if v.bit_count()%2==(size-1)%2:end[side,v]=pool.id(("e",side,v))
    enc={"totalizer":EncType.totalizer,"sequential":EncType.seqcounter}[encoding]
    def equals(sat,lits,bound):sat.append_formula(CardEnc.equals(lits,bound=bound,vpool=pool,encoding=enc).clauses)
    def atmost(sat,lits,bound):
        if bound<len(lits):sat.append_formula(CardEnc.atmost(lits,bound=bound,vpool=pool,encoding=enc).clauses)
    def squares(side):
        for b,c in combinations(range(8),2):
            mask=(1<<b)|(1<<c)
            for v in range(256):
                if v&mask==0:yield [-selected[side,x] for x in (v,v^(1<<b),v^(1<<c),v^mask)]
    with Solver(name="cadical195",with_proof=checker is not None) as engine:
        clauses=[]
        if checker is None:sat=engine
        else:
            class Capture:
                def add_clause(self,c):clauses.append(c);engine.add_clause(c)
                def append_formula(self,cs):
                    for c in cs:self.add_clause(c)
                def __getattr__(self,k):return getattr(engine,k)
            sat=Capture()
        # Both parts start at zero. This single shared base address creates the
        # one crossing; all other address overlaps must be excluded.
        for v in range(1,256):sat.add_clause([-selected[0,v],-selected[1,v]])
        for side,size in enumerate(sizes):
            sat.add_clause([selected[side,0]])
            previous=set(old[side])
            lits=[-selected[side,v] for v in sorted(previous)]
            atmost(sat,lits,freedom)
            caps[side]=len(previous)
            for parity in (0,1):
                ls=[selected[side,v] for v in range(256) if v.bit_count()%2==parity]
                equals(sat,ls,(size+(1-parity))//2)
            endpoints=[l for (s,v),l in end.items() if s==side]
            sat.add_clause(endpoints);atmost(sat,endpoints,1)
            for v in range(256):
                s=selected[side,v];e=end.get((side,v))
                ns=[selected[side,v^(1<<b)] for b in range(8)]
                sat.add_clause([-s,*ns])
                for triple in combinations(ns,3):sat.add_clause([-s,*[-x for x in triple]])
                if v==0 or e:
                    if e:sat.add_clause([-e,s])
                    for x,y in combinations(ns,2):sat.add_clause(([-e] if e else [])+[-s,-x,-y])
                if v:
                    for i in range(8):
                        sat.add_clause([-s]+([e] if e else [])+ns[:i]+ns[i+1:])
            for c in squares(side):sat.add_clause(c)
        dynamic=[];witness=None;status="OPEN"
        while True:
            remain=budget-sat.accum_stats()["conflicts"]
            if remain<=0:break
            sat.conf_budget(remain);answer=sat.solve_limited()
            if answer is not True:
                status="UNSAT" if answer is False else "OPEN";break
            model_positives=set(sat.get_model());legs=[];added=False
            for side,size in enumerate(sizes):
                A={v for v in range(256) if selected[side,v] in model_positives}
                assert len(A)==size and len(set(old[side])-A)<=freedom
                remain_set=set(A);ordered=[0];remain_set.remove(0)
                while True:
                    nexts={ordered[-1]^(1<<b) for b in range(8)}&remain_set
                    if not nexts:break
                    assert len(nexts)==1
                    v=nexts.pop();ordered.append(v);remain_set.remove(v)
                legs.append(ordered)
                while remain_set:
                    u=remain_set.pop();cycle={u};todo=[u]
                    while todo:
                        v=todo.pop()
                        ns={v^(1<<b) for b in range(8)}&remain_set
                        remain_set-=ns;cycle|=ns;todo.extend(ns)
                    assert all(sum((v^(1<<b)) in cycle for b in range(8))==2 for v in cycle)
                    sat.add_clause([-selected[side,v] for v in sorted(cycle)])
                    dynamic.append([side,sorted(cycle)]);added=True
            if not added:
                path=legs[0][::-1]+[v|256 for v in legs[1]]
                assert len(path)==sum(sizes) and not defects(path)
                witness=path;status="FOUND";break
        row=dict(seed=seed,source=record["sources"],sizes=sizes,freedom=freedom,
                 budget=budget,encoding=encoding,status=status,stats=sat.accum_stats(),
                 dynamic_cycles=dynamic,vertices=witness)
        if checker and status=="UNSAT":
            import gzip,shutil,subprocess
            from pysat.solvers import pysolvers
            from proof_ascii import write_ascii
            from rerun_deep_certificate import digest
            prefix=Path(f"joint-cert-{tag or seed}-{freedom}-{sizes[0]}")
            cnf=prefix.with_suffix(".cnf");drat=prefix.with_suffix(".drat");core=prefix.with_suffix(".core")
            with cnf.open("w",newline="\n") as f:
                f.write(f"p cnf {max(abs(v) for c in clauses for v in c)} {len(clauses)}\n")
                for c in clauses:f.write(" ".join(map(str,c))+" 0\n")
            s=engine.solver;pysolvers.flushpr(s.prfp);s.prfile.seek(0)
            with drat.open("wb") as f:write_ascii(s.prfile,f)
            for args in ([str(cnf),str(drat),"-l",str(core)],[str(cnf),str(core)]):
                check=subprocess.run([str(checker),*args],capture_output=True)
                assert check.returncode==0 and b"s VERIFIED" in check.stdout.splitlines()
            row["checker"]=check.stdout.decode(errors="replace").splitlines()[-10:]
            for file in (cnf,core):
                row[file.suffix[1:]+"_sha256"]=digest(file)
                with file.open("rb") as f,Path(str(file)+".gz").open("wb") as dst:
                    with gzip.GzipFile(fileobj=dst,mode="wb",filename="",mtime=0,compresslevel=4) as gz:
                        shutil.copyfileobj(f,gz)
    flag=("-positive" if positive else "")+("-checked" if checker else "")
    save(Path(f"joint-faces-{tag or seed}-{freedom}-{sizes[0]}-{encoding}{flag}.json"),row)
    print(seed,freedom,sizes,status,row["stats"]["conflicts"],len(dynamic),flush=True)
    return row


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("seed",type=int);parser.add_argument("freedom",type=int)
    parser.add_argument("--budget",type=int,default=600000)
    parser.add_argument("--short-first",action="store_true")
    parser.add_argument("--encoding",default="totalizer")
    a=parser.parse_args();solve(a.seed,a.freedom,a.budget,a.short_first,a.encoding)
