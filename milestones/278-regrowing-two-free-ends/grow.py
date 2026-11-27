"""Exact lower-tail extensions for all archive charts sharing the retained middle and prefixes."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from archive import HERE, cases, write, read, lift, code

def independent_check(p):
    assert all(0<=v<512 for v in p) and len(p)==len(set(p))
    assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
    sites = {v:i for i,v in enumerate(p)}
    assert all(abs(j-sites[w])==1 for j,v in enumerate(p) for i in range(9) if (w:=v^(1<<i)) in sites)

def grow(width, budget, minimum, swap, full=False):
    groups, known, report = cases(width,minimum,full)
    ids = sorted(groups)
    tag = "%d-%d"%(minimum,width)+("-cube" if full else "")
    if swap: tag += "-reverse"
    ordered=lambda s:",".join(map(str,s))
    result = {}; representatives={}; splits=Counter()
    with TemporaryDirectory(prefix="q9tails-") as scratch:
        temp=Path(scratch); exe=temp/"ends.exe"; inputs=temp/"inputs"; results=temp/"results"
        subprocess.run(["C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe","/nologo","/optimize+","/out:"+str(exe),str(HERE/"Ends.cs")],check=True)
        text=[]
        for k in ids:
            q=groups[k]
            left,mid,right=q["a"],q["m"],q["b"]
            if swap: left,mid,right=right,mid[::-1],left
            text.append("\t".join([sha256(k).hexdigest(), ordered(left), ordered(mid), ordered(right)]))
        inputs.write_text("\n".join(text)+"\n",encoding="ascii")
        subprocess.run([str(exe),str(inputs),str(results),str(budget),"191","full" if full else "lower"],check=True)
        by_id={sha256(k).hexdigest():groups[k] for k in ids}
        with results.open() as stream:
            for line in stream:
                t=line.strip().split("\t")
                typ,ident=t[:2]; q=by_id[ident]
                if typ=="P":
                    joined=list(map(int,t[2].split(",")))
                    physical=joined if full else [lift(q["axis"],q["origin"],v) for v in joined]
                    word=code(physical)
                    if word not in representatives:
                        independent_check(physical)
                        representatives[word]=dict(edges=len(physical)-1,archive=known.get(word),vertices=physical,case=ident)
                else:
                    assert typ=="S"
                    closed,visits,best,path,saved,hist=t[2:]
                    projected=list(map(int,path.split(",")))
                    if swap: projected.reverse()
                    p=projected if full else [lift(q["axis"],q["origin"],v) for v in projected]
                    independent_check(p)
                    base=len(q["a"])+len(q["b"])+len(q["m"])-1
                    assert int(best)==len(p)-1
                    h=list(map(int,hist.split(",")))
                    assert len(h)==int(best)-base+1
                    if closed=="1": assert int(best)>=q["donor_max"]
                    result[ident]=dict(source=q["source"],axis=q["axis"],occurrences=q["occurrences"],closed=closed=="1",
                        visits=int(visits),maximum_seen=int(best),donor_maximum=q["donor_max"],base=base,
                        histogram=h,saved=int(saved),witness=p)
                    splits[(len(q["m"])-1,int(best),closed=="1")]+=1
    report.update(width=width,minimum=minimum,budget_per_case=budget,reverse=swap,
        completed=sum(r["closed"] for r in result.values()),cases=len(result),visits=sum(r["visits"] for r in result.values()),
        maxima=dict(Counter(r["maximum_seen"] for r in result.values() if r["closed"])),
        records=len(representatives),outside_archive=sum(v["archive"] is None for v in representatives.values()),
        capture_complete=all(sum(r["histogram"][max(0,191-r["base"]):])==r["saved"] for r in result.values()))
    write("summary-"+tag+".json",report)
    write("cases-"+tag+".json",result)
    write("paths-"+tag+".json",{sha256(k).hexdigest():v for k,v in representatives.items()})
    print(report,flush=True)
    if representatives and max(v["edges"] for v in representatives.values())>=192:
        write("candidate-192.json",max(representatives.values(),key=lambda v:v["edges"]))

if __name__=="__main__":
    ap=ArgumentParser(); ap.add_argument("width",type=int); ap.add_argument("--budget",type=int,default=200000)
    ap.add_argument("--minimum",type=int,default=190); ap.add_argument("--reverse",action="store_true"); ap.add_argument("--cube",action="store_true")
    a=ap.parse_args(); grow(a.width,a.budget,a.minimum,a.reverse,a.cube)

