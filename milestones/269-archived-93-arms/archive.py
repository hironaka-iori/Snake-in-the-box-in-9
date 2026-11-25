"""Reconstruct every distinguished crossing in the raw 190- and 191-edge archives."""
from collections import Counter,defaultdict
from hashlib import sha256
from pathlib import Path
import sys
from opposite import HERE,MS,read,write
from catalogue import label,identifier
from exchange import input_paths
from verify269 import previous

def cut(seq,i,d):
    # Drop dimension d and translate the crossing to zero in the two faces.
    def face(p):
        def image(x):
            y=x^p[0]
            return (y&((1<<d)-1)) | ((y>>(d+1))<<d)
        return [image(x) for x in p]
    return face(seq[:i+1][::-1]),face(seq[i+1:])

def main():
    full=read(MS/"266-rebuilding-one-arm/parents.json")["parents"]
    a266=read(MS/"266-rebuilding-one-arm/summary.json")
    a267=set(read(MS/"267-fixed-arm-extensions/summary.json")["coverage"])
    a268=read(MS/"268-archived-94-arms/summary.json")["targets"]
    a269=read(HERE/"summary.json")["roots"]
    upper98=read(MS/"252-shorter-reference-segments/replay-68-192.json")
    parents98=set(read(MS/"252-shorter-reference-segments/census-68.json")["all_ids"])
    assert upper98["all_excluded"]
    # The two other archived 96-edge shapes have sharper two-endpoint caps.
    old96=read(MS/"248-rooted-arm-capacity/parents.json")["rows"]
    measured=read(MS/"249-long-parent-joins/audit.json")["cases"]
    long_caps={}
    for r in old96:
        donor=r["donor_index"]
        if donor not in (99,114):continue
        sh=sha256(previous.shape(r["path"])).hexdigest()
        ends=[x for x in measured if x["donor"]==donor and x["edges"]==96]
        assert {x["endpoint"] for x in ends}=={0,1} and max(x["upper"] for x in ends)==93
        long_caps[sh]=max(96+1+x["upper"] for x in ends)
    def case(arm):
        pid=identifier(label(arm)[0])
        shape=sha256(previous.shape(arm)).hexdigest()
        n=len(arm)-1
        if n==96:
            assert shape in parents98
            bound,source=(long_caps[shape],249) if shape in long_caps else (191,252)
        elif n==95:
            assert pid in a267
            bound,source=191,267
        elif n==94 and full[pid]["from_191"]:
            if pid in a266["other_end_bounds"]:bound=a266["other_end_bounds"][pid][1]
            else:
                assert pid in a266["archived_attainers"]
                bound=191
            source=266
        elif n==94:
            # A Q8 partner has at most 98 edges. Each exclusion can lower this cap.
            bound=n+1+98
            for m,r in a268.items():
                if pid in r["covered"]:
                    bound=min(bound,n+int(m))
            source=268
        else:
            assert n==93
            bound,source=a269[pid]["upper"],269
        return dict(root=pid,shape=shape,edges=n,upper=bound,source_round=source)
    occurrences={}
    shapes={}
    tally=defaultdict(Counter)
    total_paths=Counter()
    root_counts=defaultdict(dict)
    for name,seq in input_paths():
        source_length=len(seq)-1
        total_paths[source_length]+=1
        steps=[v^w for v,w in zip(seq,seq[1:])]
        axes=[d for d in range(9) if steps.count(1<<d)==1]
        if not axes:continue
        assert previous.path_edges(seq,9)==source_length
        for d in axes:
            i=steps.index(1<<d)
            left,right=cut(seq,i,d)
            assert set(left)&set(right)=={0} and len(left)+len(right)-1==source_length
            arm_cases=[]
            for arm,other in ((left,right),(right,left)):
                loc=case(arm)
                far=case(arm[::-1])
                assert loc["shape"]==far["shape"]
                if loc["edges"]<=95:
                    key,axesmap=label(arm)
                    assert full[identifier(key)]["partners"][name]==[axesmap[v] for v in other]
                arm_cases.append(dict(at_crossing=loc,opposite_end=far))
                for row in (loc,far):
                    root_counts[row["edges"]][row["root"]]=row
                    shapes.setdefault(row["shape"],row["edges"])
            tag=name+":"+str(d)
            occurrences[tag]=dict(archive_name=name,vertices=seq,axis=d,crossing_index=i,arms=arm_cases)
            at=[c["at_crossing"]["upper"]<192 for c in arm_cases]
            both=[all(r["upper"]<192 for r in c.values()) for c in arm_cases]
            group=tally[str(source_length)+"/"+"+".join(map(str,sorted([len(left)-1,len(right)-1])))]
            group["examples"]+=1
            group["both_arms_at_original_end"]+=all(at)
            group["both_arms_at_both_ends"]+=all(both)
            group["excluded_endpoint_occurrences"]+=sum(r["upper"]<192 for c in arm_cases for r in c.values())
    recorded=read(MS/"265-joint-arm-regrowth/exchange.json")
    source_ids={r["name"]+":"+str(r["axis"]) for r in recorded["starts"]}
    assert sum(total_paths.values())==1173 and set(occurrences)==source_ids
    assert len({r["archive_name"] for r in occurrences.values()})==len(occurrences)==398
    assert sum(g["examples"] for n,g in tally.items() if n.startswith("190/"))==373
    assert len({c["at_crossing"]["shape"] for r in occurrences.values() if len(r["vertices"])==191
                for c in r["arms"] if c["at_crossing"]["edges"]==96})==7
    # Transport each bank partner onto a raw 190-edge snake, keeping the actual
    # parent vertices and the original crossing edge unchanged.
    bank_candidates=defaultdict(dict)
    for record in occurrences.values():
        path=record["vertices"]
        if len(path)!=192:continue
        d,i=record["axis"],record["crossing_index"]
        left,right=cut(path,i,d)
        for arm,other in ((left,right),(right,left)):
            normalized,axes=label(arm)
            word=tuple(axes[v] for v in other)
            bank_candidates[identifier(normalized)][word]=record["archive_name"]
    direct_matches={}
    example=None
    for tag,r in occurrences.items():
        path=r["vertices"]
        if len(path)!=191:continue
        i,d=r["crossing_index"],r["axis"]
        left,right=cut(path,i,d)
        matches={}
        for side,arm in enumerate((left,right)):
            normalized,axes=label(arm)
            available=bank_candidates.get(identifier(normalized),{})
            if not available:continue
            inverse={u:v for v,u in enumerate(axes)}
            centre=path[i+1] if side==0 else path[i]
            def lift(v):
                u=inverse[v]
                return centre^(u%2**d + ((u>>d)<<(d+1)))
            found={}
            for word,name in sorted(available.items()):
                replacement=[lift(v) for v in word]
                result=(path[:i+1]+replacement) if side==0 else (replacement[::-1]+path[i+1:])
                assert previous.path_edges(result,9)==191
                assert previous.shape(result)==previous.shape(occurrences[next(x for x,z in occurrences.items() if z["archive_name"]==name)]["vertices"])
                found[name]=sha256(b"".join(v.to_bytes(2,"little") for v in result)).hexdigest()
                if example is None:
                    example=dict(source=r["archive_name"],matching_record=name,source_path=path,rebuilt_path=result,
                                 side_retained="left" if side==0 else "right",crossing=[path[i],path[i+1]],
                                 fixed_parent=path[:i+1] if side==0 else path[i+1:],
                                 edges_before=190,edges_after=191,verified_pairs=18336)
            matches[str(side)]=found
        if matches: direct_matches[tag]=matches
    assert example is not None
    write(HERE/"rebuild-190-to-191.json",example)
    exact_44={}
    for tag,r in occurrences.items():
        if sorted(c["at_crossing"]["edges"] for c in r["arms"])!=[93,96]:continue
        cap=max(row["upper"] for c in r["arms"] for row in c.values())
        attained=191 if tag in direct_matches else 190
        assert cap==attained
        exact_44[tag]=cap
    assert len(exact_44)==44
    input_paths_=["248-rooted-arm-capacity/parents.json","249-long-parent-joins/audit.json",
                  "252-shorter-reference-segments/replay-68-192.json","252-shorter-reference-segments/census-68.json",
                  "265-joint-arm-regrowth/exchange.json","266-rebuilding-one-arm/summary.json",
                  "267-fixed-arm-extensions/summary.json","268-archived-94-arms/summary.json",HERE.name+"/summary.json"]
    raw_sources=read(MS/"244-190-path-construction/results.json")["member_sha256"]
    root_summary={n:dict(roots=len(rs),excluded=sum(r["upper"]<192 for r in rs.values()),
                     shapes=len({r["shape"] for r in rs.values()})) for n,rs in sorted(root_counts.items())}
    out=dict(sources={f:sha256((MS/f).read_bytes()).hexdigest() for f in input_paths_},
              bank191_sha256=sha256((MS.parent/"work/bank9.json").read_bytes()).hexdigest(),
              archive190_member_sha256=raw_sources,archive_counts=total_paths,groups=tally,unique_roots=root_summary,
              snake_count=len(occurrences),endpoint_occurrences=4*len(occurrences),bank_rebuilds=direct_matches,exact_93_96_family_maxima=exact_44,examples=occurrences)
    write(HERE/"archive.json",out)
    print("Groups",dict(tally),"unique roots",root_summary)
if __name__=="__main__":main()
