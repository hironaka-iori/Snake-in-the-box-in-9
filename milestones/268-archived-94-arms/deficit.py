"""Remove free-endpoint selectors by counting the degree sum of each parity class."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
import search
from search import HERE, bank, read, write, rebuild, roots, aligned


def model(blocked, length, prefix, cycles, seen):
    graph = rebuild.geometry
    assert prefix[0] == 0 and not set(prefix).intersection(blocked)
    graph.verify(prefix,8)
    cnf = graph.Formula()
    chosen = {v:cnf.variable() for v in range(256) if v not in blocked}
    for side,count in ((0,length//2+1),(1,(length+1)//2)):
        cnf.exactly([lit for v,lit in chosen.items() if v.bit_count()%2==side],count)
    cnf.clauses.append([chosen[0]])
    for v,lit in chosen.items():
        neighbours = [chosen[w] for w in graph.NEIGHBOURS[v] if w in chosen]
        if v == 0:
            graph.bounds(cnf,neighbours,1,1,[])
        elif v.bit_count()%2 == length%2:
            # The sum on this side has just one unit of deficit after accounting for zero.
            graph.bounds(cnf,neighbours,0,2,[-lit])
        else:
            graph.bounds(cnf,neighbours,2,2,[-lit])
    for i,v in enumerate(prefix):
        cnf.clauses.append([chosen[v]])
        if i+1 < len(prefix):
            adjacent = set(prefix[max(0,i-1):i]+prefix[i+1:i+2])
            cnf.clauses.extend([-chosen[w]] for w in graph.NEIGHBOURS[v] if w in chosen and w not in adjacent)
    graph.face_bounds(cnf,chosen)
    cnf.clauses.extend(graph.cycle_clause(chosen,c) for c in cycles)
    for path in seen:
        assert path[0]==0 and len(path)==length+1 and not set(path).intersection(blocked)
        graph.verify(path,8)
        cnf.clauses.append([-chosen[v] for v in sorted(path)])
    return cnf,chosen


def main():
    cli=ArgumentParser()
    cli.add_argument("--length",type=int,default=97)
    cli.add_argument("--seconds",type=float,default=8)
    cli.add_argument("--published",action="store_true")
    cli.add_argument("--only",type=int,nargs="+")
    args=cli.parse_args()
    source,images=roots(),list(bank.permutation_images())
    groups=read(HERE/"groups.json")
    file=HERE/f"queries-{args.length}.json"
    ledger=read(file) if file.exists() else {}
    search.base_model=model
    with TemporaryDirectory() as d:
        tmp=Path(d)
        tools=rebuild.masks.compilers(tmp)
        for i,g in enumerate(groups):
            old=ledger.get(str(i),{})
            if old.get("status") in ("witness","excluded") or args.only and i not in args.only:
                continue
            if args.published and not any(source[k]["partners"] for k in g["ranks"]):
                continue
            ans=search.query(g,source,images,args,tmp,tools,old)
            ans["encoding"]="parity-deficit"
            ledger[str(i)]=ans
            write(file,ledger)
            print(i,len(g["ranks"]),args.length,ans["status"],flush=True)
            if ans["status"]=="witness" and args.length>=97:return

if __name__=="__main__":
    main()
