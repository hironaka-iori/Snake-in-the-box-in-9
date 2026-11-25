"""Search the whole opposite face at the endpoints of the reconstructed Q8 parents."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path
from tempfile import TemporaryDirectory
from hashlib import sha256
from itertools import permutations
import sys
HERE=Path(__file__).resolve().parent
MS=HERE.parent
R270=next(MS.glob("270-*"))
sys.path.insert(0,str(MS/"269-archived-93-arms"))
from opposite import translate_domains,legal_next,aligned,family_model,rebuild,read,write,bank,pack
import search
import deficit
from verify269 import previous as original_audit, next_sites
from transport271 import build_transfers, verify_transfers

def cases():
    roots=read(R270/"opposite-constructions.json")["roots"]
    return roots

def plan():
    source=cases()
    images=list(bank.permutation_images())
    groups=[]
    transfers=build_transfers(HERE,MS,source,images)
    for n in sorted({len(r["parent"])-1 for r in source.values()},reverse=True):
        part={k:r["parent"] for k,r in source.items() if len(r["parent"])==n+1}
        if n < 93:
            # Even a maximum Q8 partner of 98 edges falls below 192 here.
            pieces=[dict(ranks={k:0},blocked=sorted(p[1:])) for k,p in part.items()]
        else:
            pieces=pack(part,images,n-6)
        for g in pieces:
            g["length"]=n
            groups.append(g)
    def priority(g):
        keys=g["ranks"]
        live=[k for k in keys if transfers.get(k,{}).get("ceiling",999)>=192]
        return (-g["length"],not any(source[k]["history"] for k in live),
                -max((source[k]["best"]["edges"] for k in live),default=0),-len(live),min(keys))
    groups.sort(key=priority)
    write(HERE/"groups.json",groups)
    print("Groups by length",Counter(g["length"] for g in groups),"groups",len(groups),"roots",len(source))

def proof_search(opt):
    groups=read(HERE/"groups.json");roots=cases()
    images=list(bank.permutation_images())
    dest=HERE/("queries-"+str(opt.target)+".json")
    ledger=read(dest) if dest.exists() else {}
    inherited=read(HERE/"transfers.json")["roots"]
    if opt.deficit:search.base_model=deficit.model
    with TemporaryDirectory() as tmpdir:
        tmp=Path(tmpdir);tools=rebuild.masks.compilers(tmp)
        for i,g in enumerate(groups):
            if g["length"] not in opt.parents or opt.only and i not in opt.only:continue
            actual=aligned(g,roots,images)
            chosen={k:p for k,p in actual.items() if (not opt.controls or roots[k]["history"]) and
                    (not opt.improve_only or roots[k]["best"]["edges"]<opt.target) and
                    inherited.get(k,{}).get("ceiling",999)>=opt.target and len(p)+98>=opt.target}
            if not chosen:continue
            n=opt.target-1-g["length"]
            tag=",".join(chosen)
            job=ledger.setdefault(tag,dict(group=i,keys=list(chosen),rows={}))
            assert job["group"]==i and job["keys"]==list(chosen)
            rows=job["rows"]
            def run_prefix(path):
                domains=translate_domains(chosen,path)
                if not domains:return
                for other in ledger.values():
                    if other["group"]==i and domains.keys()<=set(other["keys"]):
                        if any(other["rows"].get(",".join(map(str,path[:t])),{}).get("status")=="excluded"
                               for t in range(1,len(path)+1)):return
                if len(path)<=opt.depth:
                    for v in legal_next(path):run_prefix(path+[v])
                    return
                addr=",".join(map(str,path));old=rows.get(addr,{})
                if old.get("status")=="witness":return
                sites=list(domains.values());common=set.intersection(*sites)
                rebuild.model=family_model(sites)
                row=rebuild.solve(HERE,tmp,tools,common,n+1-len(path),[0],old.get("cycles",[]),[],opt.seconds)
                if opt.deficit:row["encoding"]="parity-deficit"
                if row["status"]=="witness":
                    arm=path[:-1]+[v^path[-1] for v in row["path"]]
                    row["joins"]={k:p[::-1]+[256+v for v in arm] for k,p in chosen.items() if set(p)&set(arm)=={0}}
                    assert row["joins"]
                    for q in row["joins"].values():assert len(q)==opt.target+1 and bank.check_path(q,9)==(len(q)-1)*len(q)//2
                    if opt.target>=192:
                        write(HERE/"candidate-192.json",{k:undo_alignment(q,images[g["ranks"][k]])
                                                        for k,q in row["joins"].items()})
                rows[addr]=row
                write(dest,ledger)
                print(i,g["length"],opt.target,path,row["status"],flush=True)
            run_prefix([0])
            if (HERE/"candidate-192.json").exists():return

def undo_alignment(join,images):
    inverse=bytearray(256)
    for i,v in enumerate(images):inverse[v]=i
    return [(v&256)+inverse[v&255] for v in join]

def interval_bounds(roots,bounds):
    representatives={r["shape"]:r["parent"] for r in roots.values()}
    edges={}
    caps={s:max(bounds[k]["maximum"] for k,r in roots.items() if r["shape"]==s) for s in representatives}
    for s,p in representatives.items():
        children=set()
        for a in (p,p[::-1]):
            for v in range(256):
                if (v^a[-1]).bit_count()!=1 or v in a:continue
                if any((v^x).bit_count()==1 for x in a[:-1]):continue
                q=a+[v]
                assert original_audit.path_edges(q,8)==len(q)-1
                children.add(original_audit.shape(q).hex())
        edges[s]=sorted(children)
    conclusions={}
    for s in representatives:
        larger={s}
        queue=[s]
        for current in queue:
            for child in edges.get(current,[]):
                if child not in larger:queue.append(child);larger.add(child)
        missing=sorted(larger-representatives.keys())
        best=max((k for k,r in roots.items() if r["shape"] in larger),key=lambda k:(bounds[k]["minimum"],k))
        containing=roots[best]["parent"]
        vertices=len(s)//2+1
        offsets=[j for j in range(len(containing)-vertices+1)
                 if original_audit.shape(containing[j:j+vertices]).hex()==s]
        assert offsets
        conclusions[s]=dict(containing_shapes=sorted(larger),unclassified=missing,
                            minimum=bounds[best]["minimum"],attaining_lower_bound_root=best,
                            interval_offset=offsets[0],ceiling=None if missing else max(caps[z] for z in larger))
    return dict(single_extensions=edges,intervals=conclusions,
                outside_shapes=sorted({t for children in edges.values() for t in children if t not in representatives}),
                excluded_192=sum(v["ceiling"] is not None and v["ceiling"]<192 for v in conclusions.values()),
                exact_maxima=sum(v["ceiling"]==v["minimum"] for v in conclusions.values()))

def audit():
    roots=cases()
    groups=read(HERE/"groups.json")
    axes=list(permutations(range(8)))
    by_group=[]
    for g in groups:
        mapped={}
        for k,rank in g["ranks"].items():
            mapping=axes[rank]
            mapped[k]=[sum(1<<mapping[i] for i in range(8) if v&(1<<i)) for v in roots[k]["parent"]]
        assert set(g["blocked"])==set.intersection(*(set(p[1:]) for p in mapped.values()))
        by_group.append(mapped)
    assert sorted(k for g in groups for k in g["ranks"])==sorted(roots)
    ev={}
    ceilings=verify_transfers(HERE,MS,roots)
    for k,r in roots.items():
        p=r["parent"];w=r["best"]
        assert p[0]==0 and sha256(bytes(p)).hexdigest()==k and w["A"]==p
        assert original_audit.shape(p).hex()==r["shape"]
        assert w["joined"]==p[::-1]+[256+v for v in w["B"]] and original_audit.path_edges(w["joined"],9)==w["edges"]
        ev[k]=dict(parent_edges=len(p)-1,shape=r["shape"],minimum=w["edges"],
                   maximum=min(len(p)+98,ceilings.get(k,999)))
    results={}
    original_audit.HERE=HERE
    known={}
    with TemporaryDirectory() as tmpdir:
        tmp=Path(tmpdir);checker=rebuild.masks.compilers(tmp)[0]
        for f in sorted(HERE.glob("queries-*.json")):
            target=int(f.stem.split("-")[-1]);cuts={k:set() for k in roots};counts=Counter()
            for job in read(f).values():
                g=groups[job["group"]]
                parents=by_group[job["group"]]
                assert all(len(p)==g["length"]+1 for p in parents.values())
                assert sorted(set.intersection(*(set(p[1:]) for p in parents.values())))==g["blocked"]
                parents={k:parents[k] for k in job["keys"]}
                for addr,row in job["rows"].items():
                    path=list(map(int,addr.split(",")))
                    bank.check_path(path,8)
                    assert path[0]==0
                    compatible={k:p for k,p in parents.items() if set(p)&set(path)=={0}}
                    masks=[]
                    for k,p in compatible.items():
                        unusable={v for v in range(256) if v in p[1:] or any((v^u).bit_count()<=1 for u in path[:-1])}
                        unusable.discard(path[-1])
                        masks.append({v^path[-1] for v in unusable})
                    n=target-g["length"]-len(path)
                    assert masks
                    original_audit.replay(masks,n,row,tmp,checker)
                    counts[row["status"]]+=1
                    if row["status"]=="excluded":
                        for k in compatible: cuts[k].add(tuple(path))
                    elif row["status"]=="witness":
                        arm=path[:-1]+[v^path[-1] for v in row["path"]]
                        actual={k:p[::-1]+[256+v for v in arm] for k,p in parents.items() if set(p)&set(arm)=={0}}
                        assert actual==row["joins"]
                        for k,q in actual.items():
                            assert original_audit.path_edges(q,9)==target
                            inverse_axes=axes[g["ranks"][k]]
                            q=[(v&256)+sum(1<<i for i,b in enumerate(inverse_axes) if v&(1<<b)) for v in q]
                            assert q[:len(roots[k]["parent"])]==roots[k]["parent"][::-1]
                            assert original_audit.path_edges(q,9)==target
                            ev[k]["minimum"]=max(ev[k]["minimum"],target);known.setdefault(k,{})[str(target)]=q
            covered=[];incomplete={}
            for i,g in enumerate(groups):
                for k,p in by_group[i].items():
                    branches=cuts[k]
                    level=max(map(len,branches),default=0)
                    def closed(prefix):
                        if tuple(prefix) in branches:return True
                        if len(prefix)>=level:return False
                        return all(closed(prefix+[v]) for v in next_sites(prefix,p))
                    if closed([0]):
                        ev[k]["maximum"]=min(ev[k]["maximum"],target-1);covered.append(k)
                    elif branches:
                        front=[[0]]
                        for _ in range(level-1):
                            front=[q+[v] for q in front if not closed(q)
                                   for v in next_sites(q,p) if not closed(q+[v])]
                        incomplete[k]=dict(alignment_group=i,remaining_at_depth=level-1,
                                           remaining_prefixes=front)
            results[target]=dict(direct_coverage=sorted(covered),query_counts=counts,
                                 partially_excluded_roots=incomplete)
    tail_file=HERE/"tails.json"
    tail_gains={}
    witness_sources={}
    if tail_file.exists():
        tails=read(tail_file)
        for k,series in tails["roots"].items():
            r=roots[k];parent=r["parent"]
            assert r["best"]["edges"]>=tails["minimum"]
            seeds=[r["best"]["B"],r["placement"]["partner"],*r["history"].values()]
            for f in sorted(HERE.glob("matched-*.json")):
                if not f.stem.rsplit("-",1)[-1].isdigit():continue
                seeds.extend(row["best"]["B"] for tag,row in read(f).items() if tag.split(":")[0]==k and row["best"])
            retained=HERE/"retained-site-replay.json"
            if retained.exists() and k in read(retained):
                seq=read(retained)[k]["joined"]
                seeds.append([v-256 for v in seq[len(parent):]])
            for row in series:
                assert row["start"] in seeds
                q=row["joined"]
                assert q==parent[::-1]+[256+v for v in row["partner"]]
                n=original_audit.path_edges(q,9)
                assert n==row["rounds"][-1]["joined_edges"]
                kept=row["rounds"][-1]["kept_partner_edges"]+1
                assert row["partner"][:kept]==row["start"][:kept]
                if n>max(r["best"]["edges"],len(parent)+len(row["start"])-1):
                    tail_gains[k]=max(n,tail_gains.get(k,0))
                    ev[k]["minimum"]=max(ev[k]["minimum"],n)
                    known.setdefault(k,{})[str(n)]=q
                    witness_sources[(k,n)]=tail_file.name
        from tail_replay import audit_tails
        write(HERE/"tail-replay.json",audit_tails(roots,tails))
    external={}
    def accept(k,q,source,n):
        p=roots[k]["parent"]
        assert len(q)>len(p) and q[:len(p)]==p[::-1] and q[len(p)]==256
        assert all(256<=v<512 for v in q[len(p):]) and original_audit.path_edges(q,9)==n
        if n>=ev[k]["minimum"]:
            known.setdefault(k,{})[str(n)]=q
            witness_sources[(k,n)]=source
        ev[k]["minimum"]=max(ev[k]["minimum"],n)
        external.setdefault(source,{})[k]=max(n,external.get(source,{}).get(k,0))
    for f in sorted(HERE.glob("matched-*.json")):
        if not f.stem.rsplit("-",1)[-1].isdigit():continue
        for tag,row in read(f).items():
            if not row["best"]:continue
            k=tag.split(":")[0];w=row["best"]
            assert row["parent"]==w["A"]==roots[k]["parent"]
            assert w["joined"]==w["A"][::-1]+[256+v for v in w["B"]]
            accept(k,w["joined"],f.name,w["edges"])
    retained=HERE/"retained-site-replay.json"
    if retained.exists():
        for k,r in read(retained).items():accept(k,r["joined"],retained.name,r["edges"])
    new_donor=HERE/"new-donor.json"
    if new_donor.exists():
        data=read(new_donor)
        assert set(data["roots"])==set(roots)
        for k,r in data["roots"].items():
            p=roots[k]["parent"]
            b=[v-256 for v in r["joined"][len(p):]]
            donor=data["donor"][::-1] if r["source_order"] else data["donor"]
            mapping=axes[r["rank"]]
            assert b==[sum(1<<mapping[i] for i in range(8) if (v^donor[0])&(1<<i))
                       for v in donor[:r["partner_edges"]+1]]
            accept(k,r["joined"],new_donor.name,r["edges"])
    for e in ev.values():assert e["minimum"]<=e["maximum"]
    # Confirm that the membership of every parent shape includes both choices of crossing endpoint.
    for k,r in roots.items():
        p=r["parent"][::-1]
        flips=[v^w for v,w in zip(p,p[1:])]
        axes=list(dict.fromkeys(flips))
        ordered=[sum(1<<i for i,b in enumerate(axes) if (v^p[0])&b) for v in p]
        assert sha256(bytes(ordered)).hexdigest() in roots
    intervals=interval_bounds(roots,ev)
    write(HERE/"intervals.json",intervals)
    write(HERE/"additional-witnesses.json",known)
    k=max(ev,key=lambda k:(ev[k]["minimum"],k))
    n=ev[k]["minimum"]
    q=known.get(k,{}).get(str(n),roots[k]["best"]["joined"])
    pairs=bank.check_path(q,9)
    assert len(q)==n+1 and original_audit.path_edges(q,9)==n
    p=roots[k]["parent"]
    write(HERE/"best-join.json",dict(root=k,edges=n,source=witness_sources.get((k,n),
          "unrestricted search" if str(n) in known.get(k,{}) else "Round 270"),A=p,
          B=[v-256 for v in q[len(p):]],joined=q,unordered_pairs=pairs))
    archive_matches={}
    if any(t in ("190","191") for vals in known.values() for t in vals):
        from exchange import input_paths
        archive={original_audit.shape(q):name for name,q in input_paths()}
        archive_matches={k:{t:archive.get(original_audit.shape(q)) for t,q in vals.items() if t in ("190","191")}
                         for k,vals in known.items()}
    write(HERE/"summary.json",dict(roots=ev,queries=results,excluded_192=sum(r["maximum"]<192 for r in ev.values()),
            maximum_constructed=max(r["minimum"] for r in ev.values()),fixed_shapes=len({r["shape"] for r in ev.values()}),
            transferred_roots=len(ceilings),archive_matches=archive_matches,tail_improvements=tail_gains,
            independently_checked_constructions=external,
            interval_shapes_excluded_192=intervals["excluded_192"],outside_single_extensions=intervals["outside_shapes"],
            source_sha256=sha256((R270/"opposite-constructions.json").read_bytes()).hexdigest()))
    print("Coverage by length",[(n,sum(r["maximum"]<192 for r in ev.values() if r["parent_edges"]==n),sum(r["parent_edges"]==n for r in ev.values())) for n in sorted({r["parent_edges"] for r in ev.values()})])

if __name__=="__main__":
    ap=ArgumentParser()
    ap.add_argument("action",choices=["plan","search","audit"])
    ap.add_argument("--target",type=int,default=192)
    ap.add_argument("--parents",type=int,nargs="+",default=[97])
    ap.add_argument("--seconds",type=float,default=5)
    ap.add_argument("--depth",type=int,default=0)
    ap.add_argument("--deficit",action="store_true")
    ap.add_argument("--only",type=int,nargs="+")
    ap.add_argument("--controls",action="store_true")
    ap.add_argument("--improve-only",action="store_true")
    a=ap.parse_args()
    if a.action=="plan":plan()
    elif a.action=="audit":audit()
    else:proof_search(a)
