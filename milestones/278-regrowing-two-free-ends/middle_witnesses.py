"""Reconstruct every archived two-crossing middle, its attaining donor and the clause evidence."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json

from archive import HERE, MS, input_paths
from middle_clauses import reconstruct
from whole_middle import encode as production


def key(m):
    steps=[x^y for x,y in zip(m,m[1:])]
    def relabel(s):
        labels={symbol:i for i,symbol in enumerate(dict.fromkeys(s))}
        return bytes(labels[t] for t in s)
    return min(relabel(steps),relabel(steps[::-1])).hex()


def isometry(source,dest):
    """An explicit signed permutation taking source to dest as ordered, or reversed."""
    assert len(source)==len(dest)
    for backwards in (False,True):
        seq=source[::-1] if backwards else source
        pairs=[((u^v).bit_length()-1,(a^b).bit_length()-1) for u,v,a,b in zip(seq,seq[1:],dest,dest[1:])]
        partial=dict(pairs)
        if len(set(partial.values()))!=len(partial) or any(partial[x]!=y for x,y in pairs):
            continue
        missing_src=sorted(set(range(8))-partial.keys())
        missing_dst=sorted(set(range(8))-set(partial.values()))
        partial.update(zip(missing_src,missing_dst))
        perm=[partial[i] for i in range(8)]
        assert sorted(perm)==list(range(8))
        shift=dest[0]^bits(seq[0],perm)
        if all((bits(v,perm)^shift)==w for v,w in zip(seq,dest)):
            return dict(reversed=backwards,source_axis_to_target=perm,target_xor=shift)
    raise ValueError("Middle paths are inequivalent")


def bits(x,perm):
    return sum(1<<j for i,j in enumerate(perm) if (x>>i)&1)


def two_cuts(p):
    steps=[s^t for s,t in zip(p,p[1:])]
    for axis in range(9):
        bit=1<<axis
        where=[i for i,s in enumerate(steps) if s==bit]
        if len(where)!=2:continue
        a,b=where
        origin=p[a]
        perm=[d for d in range(9) if d!=axis]+[axis]
        normalized=[sum(((v^origin)>>d&1)<<i for i,d in enumerate(perm)) for v in p]
        assert all((v>>8)==int(a<i<=b) for i,v in enumerate(normalized))
        yield axis,origin,normalized,[v&255 for v in normalized[a+1:b+1]]


def geometry(seq,dimension):
    assert seq and len(set(seq))==len(seq) and all(0<=v<1<<dimension for v in seq)
    for i,v in enumerate(seq):
        for j in range(i):
            assert ((v^seq[j]).bit_count()==1)==(j==i-1)


def validate_chart(path,m):
    inside=[i for i,v in enumerate(path) if v>=256]
    a,b=inside[0],inside[-1]
    assert inside==list(range(a,b+1)) and 0<a<=b<len(path)-1
    assert [v-256 for v in path[a:b+1]]==m
    assert path[a-1]==m[0] and path[b+1]==m[-1]
    return [a-1,len(path)-b-2]


def main():
    query_file=HERE/"whole-middle.json"
    saved=json.loads(query_file.read_bytes())
    groups={}
    for label,p in input_paths():
        for axis,origin,raw,m in two_cuts(p):
            k=key(m)
            dest=saved[k]["m"] if k in saved else groups.get(k,{}).get("m",m)
            entry=groups.setdefault(k,dict(m=dest,counts=Counter(),record_names=set(),winners={}))
            entry["counts"][len(p)-1]+=1
            if len(p)==192:entry["record_names"].add(label)
            mapping=isometry(m,dest)
            full_perm=mapping["source_axis_to_target"]+[8]
            placed=[bits(v,full_perm)^mapping["target_xor"] for v in raw]
            if mapping["reversed"]:placed.reverse()
            arms=validate_chart(placed,dest)
            drop_order=[d for d in range(9) if d!=axis]+[axis]
            to_raw={bits(v,full_perm)^mapping["target_xor"]:bits(v,drop_order)^origin for v in raw}
            recovered=[to_raw[v] for v in placed]
            assert (recovered[::-1] if mapping["reversed"] else recovered)==p
            criterion=(len(p)-1,placed[0].bit_count()%2 if (len(p)-1)%2==0 else 0)
            if criterion not in entry["winners"]:
                entry["winners"][criterion]=dict(source=label,archive_axis=axis,archive_origin=origin,
                    compressed_middle_to_query=mapping,outer_edges=arms,archive_vertices=p,query_vertices=placed)
    assert len(groups)==22 and set(saved)<=groups.keys()
    rows={}
    outcomes=Counter()
    excluded_count=0
    positive_count=0
    for k,item in sorted(groups.items()):
        m=item["m"]
        geometry(m,8)
        archived=max(t[0] for t in item["winners"])
        best=next(d for (n,side),d in item["winners"].items() if n==archived)
        row=saved.get(k,{})
        if row:
            assert sum(item["counts"].values())==row["occurrences"] and item["counts"][191]==row["records"]
        targets=row.get("targets",{})
        decisions={}
        union_cuts={}
        upper=None
        lower=archived
        for label,z in sorted(targets.items()):
            n=z["target"]; side=z["majority_if_even"]
            assert label==f"{n}-{side}"
            for c in z["cycles"]:union_cuts[tuple(sorted(c))]=c
            four=z.get("four_cube_caps",False)
            take={"status":z["status"],"four_cube_caps":four}
            if z["status"]=="excluded":
                receipt=reconstruct(m,n,side,z["cycles"],four=four)
                assert receipt["cnf"]==z["cnf"] and receipt["clauses"]==z["clauses"]
                assert sha256((HERE/z["proof"]).read_bytes()).hexdigest()==z["compressed"]
                take.update(semantic_cnf=receipt,proof_sha256=z["compressed"])
                excluded_count+=1
            if z["status"]=="witness":
                s=z["path"]
                assert len(s)==n+1
                geometry(s,9)
                try:validate_chart(s,m)
                except AssertionError:validate_chart(s[::-1],m)
                if n%2==0:assert s[0].bit_count()%2==side==s[-1].bit_count()%2
                lower=max(lower,n)
            decisions[label]=take
        for n in {v["target"] for v in targets.values()}:
            if n<len(m)+1:continue
            parities=(0,1) if n%2==0 else (0,)
            if all(targets.get(f"{n}-{p}",{}).get("status")=="excluded" for p in parities):
                upper=n-1 if upper is None else min(upper,n-1)
        assert upper is None or lower<=upper
        exact=lower if upper==lower else None
        outcomes[exact]+=1
        controls=[]
        for (n,side),donor in sorted(item["winners"].items()):
            s=donor["query_vertices"]
            geometry(donor["archive_vertices"],9)
            geometry(s,9)
            assert n==sum(donor["outer_edges"])+len(m)+1
            cycles=list(union_cuts.values())
            for four in ([False,True] if any(z.get("four_cube_caps") for z in targets.values()) else [False]):
                receipt=reconstruct(m,n,side,cycles,s,four=four)
                cnf,_=production(m,n,side,cycles,four)
                with TemporaryDirectory() as scratch:
                    digest=cnf.save(Path(scratch)/"donor.cnf")
                assert digest==receipt["cnf"] and len(cnf.clauses)==receipt["clauses"] and cnf.count==receipt["variables"]
                del cnf
                controls.append(dict(source=donor["source"],axis=donor["archive_axis"],edges=n,four_cube_caps=four,
                    endpoint_majority_if_even=side if n%2==0 else None,checked_satisfying_assignment=receipt))
                positive_count+=1
        rows[k]=dict(middle_edges=len(m)-1,m=m,occurrences_by_path_length=dict(item["counts"]),
            distinct_archived_191_sources=sorted(item["record_names"]),best_archived_edges=archived,
            best_archived=best,decisions=decisions,independent_positive_controls=controls,
            lower_bound=lower,upper_bound=upper,exact_maximum=exact)
    historical=next(MS.glob("188-*/data/lift8to9-fixed95.json"))
    old=json.loads(historical.read_bytes())
    assert old["status"]=="UNKNOWN" and old["target_edges"]==192 and old["middle_edges"]==95
    old_key=key(old["middle"])
    old_map=isometry(old["middle"],rows[old_key]["m"])
    prior=dict(source=historical.relative_to(MS.parent).as_posix(),sha256=sha256(historical.read_bytes()).hexdigest(),
        old_status=old["status"],middle_key=old_key,literal_old_to_current=old_map,
        vertices_equal_after_transport=len(old["middle"]),current_lower=rows[old_key]["lower_bound"],
        current_upper=rows[old_key]["upper_bound"])
    summary=dict(middle_shapes=len(groups),archived_chart_occurrences=sum(sum(x["counts"].values()) for x in groups.values()),
        independently_regenerated_exclusion_formulas=excluded_count,complete_donor_assignments=positive_count,
        exact_maxima={str(k):v for k,v in outcomes.items() if k is not None},undetermined=outcomes[None],
        round188=prior)
    out=dict(summary=summary,whole_middle_sha256=sha256(query_file.read_bytes()).hexdigest(),rows=rows)
    (HERE/"whole-middle-witnesses.json").write_text(json.dumps(out,separators=(",",":"))+"\n",encoding="utf8")
    print(json.dumps(summary))

if __name__=="__main__":
    main()
