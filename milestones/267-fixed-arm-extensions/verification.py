"""Reconcile the inherited roots, whole-domain certificates, search families and witnesses."""
from collections import Counter
from pathlib import Path
from tempfile import TemporaryDirectory
import sys

from prepare import HERE, MS, LAST, read, write, bank, label, identifier,shape_id
from families import grouped_inputs, formula as enumeration, classify, masks
from strengthen import builder, exclusions
from cuts import catalogue
from suffixes import residual,shifted_cuts
from rebuild import model,geometry
sys.path.insert(0,str(MS/"265-joint-arm-regrowth"))
from conditional import code

def key_for(path):
    return identifier(label(path)[0])

def main():
    data=read(HERE/"cases.json")
    roots=data["roots"]
    short=read(LAST/"parents.json")["parents"]
    historical=read(LAST/"summary.json")
    long_ids=set(read(MS/"252-shorter-reference-segments/census-68.json")["all_ids"])
    assert read(MS/"252-shorter-reference-segments/replay-68-192.json")["all_excluded"]
    covered=set()
    upper190=set()
    for k,why in data["inherited"].items():
        p=roots[k]["parent"]
        if why["reason"]=="94-edge census":
            ref=key_for(p[:95])
            assert ref==why["source"] and len(p)==96
            arms=[q for q in short[ref]["partners"].values() if len(q)==97]
            assert not any(set(q).isdisjoint(p[1:]) for q in arms)
            assert ref in historical["archived_attainers"] or ref in historical["other_end_bounds"]
        else:
            assert len(p)==97 and shape_id(p)==why["source"] and why["source"] in long_ids
        covered.add(k)
    old={name:tuple(mask) for mask,name in catalogue().items()}
    images=list(bank.permutation_images())
    cuts=read(HERE/"cuts.json")
    family=read(HERE/"families.json")
    stronger=read(HERE/"strengthened.json")
    direct=read(HERE/"direct-192.json")
    suffix_data=read(HERE/"suffixes.json") if (HERE/"suffixes.json").exists() else {}
    open_steps={}
    counts=Counter()
    bank9={code(r["vertex_sequence"]):i for i,r in enumerate(read(MS.parent/"work/bank9.json"))}
    with TemporaryDirectory() as d:
        tmp=Path(d)
        checker=masks.compilers(tmp)[0]
        for name,g in data["groups"].items():
            aligned,common,extras=grouped_inputs(data,g,images)
            for cut in cuts[name]:
                expected=set(bytes(old[cut["source"]]).translate(images[cut["rank"]]))-common
                assert expected==set(cut["sites"])
            if any(not c["sites"] for c in cuts[name]):
                covered.update(aligned)
                if len(next(iter(aligned.values())))==96:upper190.update(aligned)
            r=family.get(name,dict(queries={},witnesses=[]))
            for w in r["witnesses"]:
                assert classify(w["path"],aligned)==w["compatible"]
            for row in r["queries"].values():
                assert row["blocked"]==sorted(common) and row["alternatives"]==extras
                masks.replay(HERE,tmp,checker,row,builder=enumeration(r["witnesses"][:row["prior_witnesses"]]))
                counts["base_"+row["status"]]+=1
            if not r["witnesses"] and r["queries"].get("0",{}).get("status")=="excluded":
                covered.update(aligned)
                if len(next(iter(aligned.values())))==96:upper190.update(aligned)
            if name not in stronger:continue
            q=stronger[name]
            negative=exclusions(extras)
            assert [list(x) for x in negative]==q["negative"]
            assert all(all(set(s)&set(e) for e in extras) for s in negative)
            for row in q["queries"].values():
                assert row["blocked"]==sorted(common) and row["alternatives"]==extras
                masks.replay(HERE,tmp,checker,row,builder=builder(cuts[name],negative))
                counts["strengthened_"+row["status"]]+=1
                if row["status"]=="witness":
                    assert classify(row["path"],aligned)==row["compatible"]
            feasible=[f"0,{1<<j}" for j in range(8) if any((1<<j) not in p for p in aligned.values())]
            full=q["queries"].get("0",{}).get("status")=="excluded" or all(q["queries"].get(k,{}).get("status")=="excluded" for k in feasible)
            if full:
                covered.update(aligned)
                if len(next(iter(aligned.values())))==96:upper190.update(aligned)
        for row in direct.values():
            parents={k:list(bytes(roots[k]["parent"]).translate(images[rank])) for k,rank in row["ranks"].items()}
            common=set.intersection(*(set(p[1:]) for p in parents.values()))
            assert common==set(row["blocked"]) and all(row["length"]+len(p)==192 for p in parents.values())
            cnf,_=model(common,row["length"],row["prefix"],row["cycles"],[])
            f=tmp/"root.cnf"
            assert cnf.save(f)==row["cnf"]
            counts["direct_"+row["status"]]+=1
            if row["status"]=="excluded":
                fp=HERE/row["proof"]
                assert masks.digest(fp)==row["compressed"] and masks.p.check_proof(f,fp,checker)==row["replay"]
                covered.update(parents)
            elif row["status"] in ("witness","relaxed_witness"):
                geometry.verify(row["path"],8)
                assert [k for k,p in parents.items() if set(p)&set(row["path"])=={0}]==row["compatible"]
        for name,entry in suffix_data.items():
            parents={k:list(bytes(roots[k]["parent"]).translate(images[rank])) for k,rank in entry["ranks"].items()}
            for tag,row in entry["steps"].items():
                s=int(tag)
                common,extras=residual(parents,s)
                assert row["blocked"]==sorted(common) and row["alternatives"]==extras
                # In the old coordinates, the suffix cannot use the original root
                # or any of its other neighbours. Equality checks both directions.
                for p,F in zip((p for p in parents.values() if s not in p),extras):
                    allowed={u for u in range(256) if u not in p and (u==s or u.bit_count()!=1)}
                    assert {u^s for u in allowed}==set(range(256))-common-set(F)
                rules=shifted_cuts(cuts[name],common,s)
                masks.replay(HERE,tmp,checker,row,builder=builder(rules,exclusions(extras)))
                counts["suffix_"+row["status"]]+=1
                for nxt,child in entry.get("children",{}).get(tag,{}).items():
                    assert child["prefix"]==[0,int(nxt)] and child["blocked"]==sorted(common) and child["alternatives"]==extras
                    masks.replay(HERE,tmp,checker,child,builder=builder(rules,exclusions(extras)))
                    counts["second_step_"+child["status"]]+=1
            for k,p in parents.items():
                missing=[s for s in geometry.NEIGHBOURS[0] if s not in p and entry["steps"].get(str(s),{}).get("status")!="excluded"]
                for s in list(missing):
                    common,_=residual({k:p},s)
                    following=[t for t in geometry.NEIGHBOURS[0] if t not in common]
                    children=entry.get("children",{}).get(str(s),{})
                    if all(children.get(str(t),{}).get("status")=="excluded" for t in following):missing.remove(s)
                if not missing:covered.add(k)
                else:open_steps[k]=missing
    wins={k for k,r in roots.items() if r["window"]}
    archives={k for k,r in roots.items() if r["archive"]}
    window_bank=read(LAST/"windows.json")["paths"].values()
    assert wins=={key_for(q) for p in window_bank if len(p)>95 for q in (p,p[::-1])}
    assert archives=={k for k,r in short.items() if r["retain_edges"]==95}
    assert all(identifier(row["parent"])==k for k,row in roots.items())
    assert len(wins)==26 and wins<=covered
    placements=read(HERE/"placements.json")["roots"]
    attainers={}
    gains=[]
    for k,r in placements.items():
        w=r["expanded_placement"]
        geometry.verify(w["joined"],9)
        if w["joined_edges"]==191:attainers[k]=bank9[code(w["joined"])]
        gains.append(w["joined_edges"]-r["original_donors"])
    witness=next(w["expanded_placement"] for k,w in placements.items() if k in wins and w["expanded_placement"]["joined_edges"]==191)
    assert any(word in (code(witness["parent"][i:i+95]) for i in range(len(witness["parent"])-94)) for word in
               {code(r["parent"]) for r in short.values() if r["from_191"]})
    write(HERE/"attaining-191.json",witness)
    details=read(HERE/"construction-audit.json")
    studied_examples={x for k in archives for x in roots[k]["partners"]}
    covered_examples={x for k in archives&covered for x in roots[k]["partners"]}
    by_shape={}
    for k in archives:
        by_shape.setdefault(shape_id(roots[k]["parent"]),set()).add(k)
    results=dict(all_endpoints=len(roots),covered_192=len(covered),open_192=sorted(set(roots)-covered),
            extension_endpoints=len(wins),extension_endpoints_covered=len(wins&covered),
            archived_95_shapes=len({shape_id(roots[k]["parent"]) for k in archives}),archived_95_endpoints=len(archives),
            archived_95_covered=len(archives&covered),upper_190_for_95_endpoints=len(upper190),
            archived_95_shapes_covered_both_ends=sum(ends<=covered for ends in by_shape.values()),
            archived_examples_with_95=len(studied_examples),archived_examples_covered_at_published_end=len(covered_examples),
            unresolved_first_steps={k:v for k,v in open_steps.items() if k not in covered},
            coverage=sorted(covered),root_certificates=counts,donor_placement_gains=sum(v>0 for v in gains),
            largest_placement_gain=max(gains),bank_191_matches=attainers,construction_audit=details)
    write(HERE/"summary.json",results)
    print({k:v for k,v in results.items() if k not in ("coverage","open_192","construction_audit")})

if __name__=="__main__":main()
