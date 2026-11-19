"""Pinned positive controls for the generic mixed-middle model."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess

from lifts import HERE, PREV, SOLVER, model, partners, verify
from middle import cuts, maps


def recover(path):
    pairs = verify(path,9)
    changes = [i for i,(u,v) in enumerate(zip(path,path[1:])) if u ^ v == 256]
    if len(changes)!=1:
        raise ValueError("Expected one crossing between Q8 faces")
    i = changes[0]
    if path[i] & 128:
        raise ValueError("The common crossing lies on the wrong y-face")
    q = path[i] & 127
    mids, lengths = [], []
    for x in (0,1):
        seq = [v & 255 for v in path if v >> 8 == x]
        if seq[-1] == q:
            seq.reverse()
        if seq[0]!=q or seq[-1] & 128:
            raise ValueError("Incorrect arm endpoints")
        yc = [j for j,(u,v) in enumerate(zip(seq,seq[1:])) if u^v==128]
        if len(yc)!=2 or any((v&128)==0 for v in seq[yc[0]+1:yc[1]+1]):
            raise ValueError("Expected a single upper middle in each arm")
        mids.append([v&127 for v in seq[yc[0]+1:yc[1]+1]])
        lengths.append(len(seq)-1)
    if set(mids[0]) & set(mids[1]):
        raise ValueError("Middles meet")
    return q,mids,lengths,pairs


def pinned(path, expected, folder):
    q,mids,lengths,pairs = recover(path)
    if any(m not in (list(e),list(e)[::-1]) for m,e in zip(mids,expected)):
        raise ValueError("The recovered middle orders differ")
    selected = set(path)
    cnf,chosen,fixed = model(expected,q,len(path)-1)
    if not fixed <= selected <= fixed | set(chosen):
        raise ValueError("Positive control outside model domain")
    cnf.clauses.extend([lit if v in selected else -lit] for v,lit in chosen.items())
    filename = folder/"pinned.cnf"
    digest = cnf.save(filename)
    proc = subprocess.run([str(SOLVER),"--plain","-q",str(filename)],capture_output=True,timeout=20)
    if proc.returncode!=10 or b"s SATISFIABLE" not in proc.stdout:
        raise ValueError(("Pinned model was not SAT",proc.returncode,proc.stderr[-400:]))
    positive = {int(t) for line in proc.stdout.splitlines() if line.startswith(b"v ")
                for t in line.split()[1:] if int(t)>0}
    if any(not any((abs(lit) in positive)==(lit>0) for lit in clause) for clause in cnf.clauses):
        raise ValueError("Returned assignment fails a pinned CNF clause")
    if fixed | {v for v,lit in chosen.items() if lit in positive} != selected:
        raise ValueError("Returned model changed the pinned vertex set")
    return dict(status="verified_pinned_SAT",edge_length=len(path)-1,arms=lengths,q=q,
                middle_lengths=[len(m)-1 for m in mids],recovered_middles=mids,
                all_pairs_verified=pairs,cnf_sha256=digest,clauses=len(cnf.clauses),
                variables=cnf.count,optional_memberships_pinned=len(chosen),path=path)


def aligned_donors(first, reference, comparison):
    donors = {}
    for row in comparison["one_crossing_pairs"]:
        for arm,other in ((row["long"],row["short"]),(row["short"],row["long"])):
            for axis,a,m,b in cuts(arm):
                for axis2,c,n,d in cuts(other):
                    if axis!=axis2:
                        continue
                    for lut,_ in maps(m,first):
                        n2=[lut[v] for v in n]
                        if n2 not in (reference,reference[::-1]):
                            continue
                        left = tuple([lut[v] for v in a[::-1]] +
                                     [128+lut[v] for v in m] + [lut[v] for v in b])
                        right = tuple(lut[v] for v in c),tuple(lut[v] for v in d)
                        donors.setdefault((left,right),row["seed"])
    return donors


def reattach(piece, port, mid, crossing, allowance, stats):
    """Keep a suffix; attach a new port by up to four Q7 edges."""
    forbidden=set(mid)-{port}
    saved = {}
    for trim in range(min(8,len(piece)-1)+1):
        suffix=list(piece[trim:])
        anchor=suffix[0]
        if set(suffix)&forbidden or (port in suffix and port!=anchor):
            continue
        if (anchor^port).bit_count()>4:
            continue
        def grow(prefix):
            if stats["bridge_prefixes"] >= allowance:
                return
            stats["bridge_prefixes"]+=1
            tip=prefix[-1]
            if tip==anchor:
                candidate=tuple(prefix+suffix[1:])
                if len(candidate)!=len(set(candidate)) or (crossing in candidate and candidate[-1]!=crossing):
                    return
                if any((u^candidate[j]).bit_count()==1 for i,u in enumerate(candidate)
                       for j in range(i+2,len(candidate))):
                    return
                saved[candidate]=None
                return
            if len(prefix)-1+(tip^anchor).bit_count()>4:
                return
            for j in range(7):
                nxt=tip^(1<<j)
                if (nxt in prefix or nxt in forbidden or (nxt in suffix and nxt!=anchor)
                        or any((nxt^v).bit_count()==1 for v in prefix[:-1])):
                    continue
                grow(prefix+[nxt])
        grow([port])
    return sorted(saved,key=lambda p:(-len(p),p))


def attempt48(first,reference,new_mids,comparison,limit):
    donors=aligned_donors(first,reference,comparison)
    stats=dict(aligned_arrangements=len(donors),bridge_prefixes=0,pairs_considered=0,
               prefix_limit=limit,maximum_bridge_edges=4,maximum_old_initial_trim=8)
    # Prioritize a middle that retains one archived port.
    new_mids=sorted(new_mids,key=lambda m:-len({m[0],m[-1]} & {reference[0],reference[-1]}))
    for mid in new_mids:
        for (left,(qpiece,epiece)),seed in donors.items():
            q=left[0]
            if qpiece[-1]!=q:
                raise ValueError("Mismatched donor roots")
            left_outer=set(v for v in left if v<128)
            for ordered in (mid,mid[::-1]):
                a=reattach(qpiece,ordered[0],ordered,q,limit,stats)
                b=reattach(epiece,ordered[-1],ordered,q,limit,stats)
                for toward_q in a:
                    if set(toward_q)&left_outer!={q}:
                        continue
                    border=set(toward_q)
                    border.update(v^(1<<j) for v in toward_q for j in range(7))
                    for toward_end in b:
                        stats["pairs_considered"]+=1
                        if len(left)+len(toward_q)+len(ordered)+len(toward_end)-1 < 188:
                            break
                        if set(toward_end)&(left_outer|border):
                            continue
                        right=list(toward_q[::-1])+[128+v for v in ordered]+list(toward_end)
                        assembled=list(left[::-1])+[256+v for v in right]
                        verify(assembled,9)
                        return assembled,[first,ordered],dict(stats,seed=seed,status="witness")
                if stats["bridge_prefixes"]>=limit:
                    return None,None,dict(stats,status="prefix_limit")
    return None,None,dict(stats,status="no_witness_in_examined_reattachments")


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--bridge-prefixes",type=int,default=250000,
                     help="Set to zero for the 191-edge pinned control alone")
    args=cli.parse_args()
    if args.bridge_prefixes<0:
        cli.error("Invalid bridge budget")
    layout_file=PREV/"middle.json"
    comparison_file=PREV/"comparison.json"
    layout=json.loads(layout_file.read_bytes())["layouts"][0]
    files=[Path(__file__),HERE/"lifts.py",PREV/"ceiling.py",PREV/"middle.py",PREV/"placements.py",
           layout_file,comparison_file,HERE/"complementary.json",SOLVER]
    result=dict(pins={p.name:sha256(p.read_bytes()).hexdigest() for p in files})
    with TemporaryDirectory(prefix="q9-247-pinned-") as temp:
        folder=Path(temp)
        record=pinned(layout["best"],layout["middles"],folder)
        if record["edge_length"]!=191 or record["middle_lengths"]!=[47,47]:
            raise ValueError("Expected the saved 191-edge control")
        result["positive_control"]=record
        if args.bridge_prefixes:
            first,candidates=partners()
            if first!=layout["middles"][0]:
                raise ValueError("Q7 reference differs")
            path,mid,stats=attempt48(first,layout["middles"][1],candidates,
                                     json.loads(comparison_file.read_bytes()),args.bridge_prefixes)
            result["local_48_search"]=stats
            if path is not None:
                result["mixed_control"]=pinned(path,mid,folder)
        else:
            result["local_48_search"]={"status":"not_requested"}
    dest=HERE/"positive-control.json"
    pending=dest.with_suffix(".tmp")
    pending.write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    pending.replace(dest)
    print("Saved positive control",record["edge_length"],record["middle_lengths"],
          "mixed search",result["local_48_search"]["status"],
          "mixed edges",result.get("mixed_control",{}).get("edge_length"))


if __name__=="__main__":
    main()
