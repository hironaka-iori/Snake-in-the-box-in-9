"""Independently reconstruct fixed short-arm charts, every unrestricted formula, and all literal joins."""
from collections import Counter
from itertools import combinations
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from fixed_short278 import HERE,FOLDER,read,write,dependencies
from archive import input_paths

def direct_lift(v,s):
    dim=s["axis"];coord=s["free_port"];axes=s["axes"]
    for i,b in enumerate(axes):
        if v & (1<<b):coord ^= 1<<i
    old=[i for i in range(9) if i!=dim]
    value=s["origin"]
    for i,a in enumerate(old):
        if coord & 1<<i:value^=1<<a
    if v&256:value^=1<<dim
    return value

def native(row,s,b):
    ordered=list(reversed(b))+[u|256 for u in row["M"]]+row["C"]
    values=[direct_lift(v,s) for v in ordered]
    return values if s["short_side"]=="right" else values[::-1]

def main():
    h=dependencies();audit=h.original_audit;audit.HERE=FOLDER
    obj=read(FOLDER/"plan.json");rr=obj["cases"]
    controls={};source_paths={};pin=sha256();chart_counts=Counter()
    for name,path in input_paths():
        source_paths[name]=path
        pin.update(name.encode()+b"\0");pin.update(b"".join(v.to_bytes(2,"little") for v in path))
        for axis in range(9):
            at=[i for i in range(len(path)-1) if path[i]^path[i+1]==1<<axis]
            if len(at)!=2:continue
            j,k=at;dims=[a for a in range(9) if a!=axis];origin=path[j]
            def project(v):return sum(1<<i for i,a in enumerate(dims) if (v^origin)&1<<a)
            left=[project(v) for v in path[:j+1]][::-1]
            mid=[project(v) for v in path[j+1:k+1]]
            right=[project(v) for v in path[k+1:]]
            for side,c,m,b in (("left",left,mid[::-1],right),("right",right,mid,left)):
                if len(c)>4:continue
                tag=(name,axis,side);assert tag not in controls
                controls[tag]=(origin,c,m,b);chart_counts[f"{len(path)-1}/{len(c)-1}"]+=1
    assert pin.hexdigest()==obj["input_archive_sha256"] and obj["charts"]==dict(chart_counts)
    registered=set();caps={};totals=Counter();targets={};positive={}
    for k,r in rr.items():
        M,C=r["M"],r["C"]
        assert k==sha256(bytes([len(M),*M,len(C),*C])).hexdigest() and M[0]==0 and M[-1]==C[0]
        banned={x for x in range(256) if (x in M[1:-1] or any((x^v).bit_count()<=1 for v in C))}
        assert 0 not in banned and banned==set(r["forbidden"])
        begins=[]
        for src in r["sources"]:
            tag=src["source"],src["axis"],src["short_side"]
            assert tag not in registered;registered.add(tag)
            origin,c,m,b=controls[tag];a=src["axes"]
            assert src["origin"]==origin and src["free_port"]==m[0] and sorted(a)==list(range(8))
            def mapped(v):return sum(1<<a[i] for i in range(8) if (v^m[0])&1<<i)
            assert list(map(mapped,m))==M and list(map(mapped,c))==C and list(map(mapped,b))==src["free_donor"]
            q=native(r,src,src["free_donor"])
            assert q==source_paths[src["source"]] and audit.path_edges(q,9)==src["edges"]
            begins.append(src["edges"])
        assert max(begins)==r["maximum_starting_length"]
        q8cap=(len(M)-1)+(len(C)-1)+2+98
        caps[k]=dict(minimum=max(begins),maximum=q8cap,q8_upper=q8cap,source_charts=len(begins))
    assert registered==set(controls) and len(registered)==sum(chart_counts.values())
    with TemporaryDirectory(prefix="q9-audit-short278-") as td:
        tmp=Path(td);checker=h.rebuild.masks.compilers(tmp)[0]
        for directory in sorted(FOLDER.glob("queries-*")):
            target=int(directory.name.split("-")[1]);tiers=Counter()
            for f in sorted(directory.glob("*.json")):
                k=f.stem;r=rr[k];F=set(r["forbidden"]);need=target-len(r["M"])-len(r["C"])
                cuts=set();entry=read(f)
                for addr,row in entry.items():
                    prefix=list(map(int,addr.split(",")));tip=prefix[-1]
                    assert prefix[0]==0 and not F&set(prefix) and audit.path_edges(prefix,8)==len(prefix)-1
                    translated={u^tip for u in range(256) if u in F or
                                (u!=tip and any((u^v).bit_count()<=1 for v in prefix[:-1]))}
                    audit.replay([translated],need+1-len(prefix),row,tmp,checker)
                    tiers[row["status"]]+=1;totals[row["status"]]+=1
                    if row["status"]=="excluded":cuts.add(tuple(prefix))
                    if row["status"]=="witness":
                        b=prefix[:-1]+[v^tip for v in row["path"]]
                        assert b==row["free_arm"] and audit.path_edges(b,8)==need and set(b).isdisjoint(F)
                        joins={}
                        for src in r["sources"]:
                            name=f"{src['source']}:{src['axis']}:{src['short_side']}"
                            q=native(r,src,b);assert audit.path_edges(q,9)==target
                            joins[name]=q
                        assert joins==row["literal_joins"]
                        positive.setdefault(k,{})[str(target)]=joins;caps[k]["minimum"]=max(caps[k]["minimum"],target)
                depth=max(map(len,cuts),default=0)
                def covered(p):
                    if tuple(p) in cuts:return True
                    if len(p)>=depth:return False
                    return all(covered(p+[x]) for x in h.next_sites(p,F|{0}))
                if covered([0]):caps[k]["maximum"]=min(target-1,caps[k]["maximum"])
            targets[target]=dict(tiers)
    assert all(row["minimum"]<=row["maximum"] for row in caps.values())
    replacements=[]
    for k,r in rr.items():
        for src in r["sources"]:
            viable=[d for d in r["sources"] if d["edges"]>src["edges"]]
            for donor in viable:
                q=native(r,src,donor["free_donor"])
                assert audit.path_edges(q,9)==donor["edges"]
                replacements.append(dict(case=k,starting_source=src["source"],axis=src["axis"],short_side=src["short_side"],
                     donor_source=donor["source"],donor_axis=donor["axis"],before=src["edges"],after=donor["edges"],ordered=q))
    archive={}
    if positive or replacements:
        archive={audit.shape(p):name for name,p in source_paths.items()}
    for row in replacements:row["archive_match"]=archive.get(audit.shape(row["ordered"]))
    write(FOLDER/"short-donor-upgrades.json",replacements)
    actual=[]
    for k,values in positive.items():
        for t,joins in values.items():
            for tag,p in joins.items():
                actual.append(dict(case=k,target=int(t),occurrence=tag,ordered=p,archive_match=archive.get(audit.shape(p))))
    hist={}
    for minimum,threshold in ((191,3),(190,3),(190,1)):
        pairs=[(k,s) for k,r in rr.items() for s in r["sources"] if s["edges"]==minimum and len(r["C"])-1<=threshold]
        hist[f"{minimum}/through{threshold}"]=dict(charts=len(pairs),fixed_cases=len({k for k,_ in pairs}),
                  excluded_192=sum(caps[k]["maximum"]<192 for k,_ in pairs),
                  exact_at_start=sum(caps[k]["maximum"]==s["edges"]==caps[k]["minimum"] for k,s in pairs))
    write(FOLDER/"summary.json",dict(source_plan_sha256=sha256((FOLDER/"plan.json").read_bytes()).hexdigest(),
          charts=chart_counts,cases=caps,verified_queries=totals,targets=targets,source_coverage=hist,
          archived_upgrades=len(replacements),upgraded_charts=len({(r["starting_source"],r["axis"],r["short_side"]) for r in replacements})))
    write(FOLDER/"positive-paths.json",actual)
    print("Independently replayed short-arm search",hist,"queries",dict(totals),"long positive charts",len(actual),flush=True)

if __name__=="__main__":main()
