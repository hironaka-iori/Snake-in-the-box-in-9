"""Classify 96-edge partners at each labelled root, starting with the published partners."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from collections import Counter
from opposite import HERE,roots,rebuild,read,write
from verify269 import previous

def main():
    ap=ArgumentParser()
    ap.add_argument("--seconds",type=float,default=4)
    ap.add_argument("--cap",type=int,default=3)
    ap.add_argument("--replay",action="store_true")
    a=ap.parse_args()
    source=roots()
    dest=HERE/"partners-96.json"
    data=read(dest) if dest.exists() else {}
    with TemporaryDirectory() as d:
        tmp=Path(d)
        tools=rebuild.masks.compilers(tmp)
        for k,r in sorted(source.items(),key=lambda kv:(not bool(kv[1]["partners"]),kv[0])):
            parent=r["parent"]
            fixed=set(parent[1:])
            seeds=sorted({tuple(w) for w in r["partners"].values()})
            assert all(len(w)==97 and previous.path_edges(parent[::-1]+[256+v for v in w],9)==190 for w in seeds)
            entry=data.setdefault(k,dict(archive_partners=[list(w) for w in seeds],additional=[],queries=[]))
            assert entry["archive_partners"]==[list(w) for w in seeds]
            queries=entry["queries"]
            if a.replay:
                seen=[list(w) for w in seeds]
                extra=[]
                for row in queries:
                    assert row["prefix"]==[0] and row["seen"]==len(seen)
                    cnf,_=rebuild.model(fixed,96,[0],row["cycles"],seen)
                    f=tmp/"replay.cnf"
                    assert cnf.save(f)==row["cnf"]
                    if row["status"]=="excluded":
                        proof=HERE/row["proof"]
                        assert rebuild.masks.digest(proof)==row["compressed"]
                        assert rebuild.masks.p.check_proof(f,proof,tools[0])==row["replay"]
                    elif row["status"]=="witness":
                        w=row["path"]
                        assert previous.path_edges(parent[::-1]+[256+v for v in w],9)==190
                        assert all(set(q)!=set(w) for q in seen)
                        seen.append(w);extra.append(w)
                assert extra==entry["additional"] and sum(q["status"]=="excluded" for q in queries)<=1
                continue
            if queries and queries[-1]["status"]=="excluded":continue
            seen=[list(w) for w in seeds]+entry["additional"]
            for _ in range(a.cap):
                old=queries[-1] if queries and queries[-1]["status"]=="open" else None
                rec=rebuild.solve(HERE,tmp,tools,fixed,96,[0],old["cycles"] if old else [],seen,a.seconds)
                rec["seen"]=len(seen)
                if old:queries[-1]=rec
                else:queries.append(rec)
                if rec["status"]=="witness":
                    w=rec["path"]
                    assert previous.path_edges(parent[::-1]+[256+v for v in w],9)==190
                    assert all(set(q)!=set(w) for q in seen)
                    seen.append(w);entry["additional"].append(w)
                write(dest,data)
                print(k[:9],rec["seen"],rec["status"],flush=True)
                if rec["status"]!="witness":break
    if a.replay:
        assert set(data)==set(source)
        known=sum(len(r["archive_partners"]) for r in data.values())
        extra=sum(len(r["additional"]) for r in data.values())
        closed=[k for k,r in data.items() if r["queries"] and r["queries"][-1]["status"]=="excluded"]
        exact={k:len(data[k]["archive_partners"])+len(data[k]["additional"]) for k in closed}
        extensions={}
        for k,entry in data.items():
            parent=source[k]["parent"]
            layer=entry["archive_partners"]+entry["additional"]
            lengths={96:len(layer)}
            for n in (97,98):
                layer=[w+[v] for w in layer for v in range(256) if v not in parent and v not in w
                       and (v^w[-1]).bit_count()==1 and all((x^v).bit_count()!=1 for x in w[:-1])]
                for q in layer:
                    joined=parent[::-1]+[256+x for x in q]
                    assert previous.path_edges(joined,9)==94+n
                    if n==98:write(HERE/"candidate-192.json",{k:joined})
                lengths[n]=len(layer)
            extensions[k]=lengths
        final=dict(archive_partners=known,additional=extra,closed_roots=closed,exact_counts=exact,
                   extensions=extensions,outcomes=Counter(q["status"] for r in data.values() for q in r["queries"]))
        write(HERE/"partner-census.json",final)
        print("96-edge census",known,extra,len(closed),final["outcomes"])
if __name__=="__main__":main()
