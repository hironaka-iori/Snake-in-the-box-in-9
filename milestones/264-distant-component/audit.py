"""Reconstruct the component coverage and count distinct maximum partners in the ordered parity experiment."""
from collections import Counter
from math import prod
from hashlib import sha256
from endpoints import HERE, MS, bank, load, save, digest, evidence, rooted, p
from census import vertices, census
from replay import columns

def adjacent(a,b): return (a^b).bit_count()==1

def support(order,length):
    selected=set(order)
    nbs={v:{v ^ (1<<j) for j in range(8)} & selected for v in range(256) if v.bit_count()%2}
    pairs=[{a,b} for a,b in zip(order,order[1:])]
    if length%2: pairs.append({order[-1]})
    return [[v for v,near in nbs.items() if near==pair] for pair in pairs]

def permitted(evens, allowed):
    live=bank.ALL_MAPS
    for v in evens[1:]: live &= allowed[v]
    return live

def reconstruct(length,words,allowed,images):
    families={}
    for s in {tuple(p[:length+1:2]) for p in words if len(p)>length}:
        live=permitted(s,allowed)
        if not live: continue
        labels=support(s,length)
        for row in labels:
            options=0
            for v in row: options |= allowed[v]
            live &= options
            if not live: break
        while live:
            bit=live & -live
            rank=bit.bit_length()-1
            mapped=tuple(images[rank][v] for v in s)
            count=prod(sum(bool(allowed[v] & bit) for v in row) for row in labels)
            if not count or families.setdefault(mapped,count)!=count:
                raise ValueError("Inconsistent multiplicities")
            live ^= bit
    return len(families),sum(families.values())

def global_coverage():
    paths, sources, _=evidence()
    data=load(HERE/"endpoints.json")
    images=list(bank.permutation_images())
    roots={}
    for shape,path in paths.items():
        for end in (0,1):
            tag=shape+":"+str(end)
            P=rooted(path,end)
            if tag in data["inherited"]:
                r=data["inherited"][tag]
                if not {images[r["rank"]][v] for v in sources[r["source"]]}<=set(P[1:]):
                    raise ValueError("Invalid earlier exclusion")
                roots[tag]="transferred"
                continue
            row=data["cases"][tag]
            if row["parent"]!=P: raise ValueError("Wrong endpoint")
            for q in row["queries"].values():
                for cycle in q["cycles"]:
                    if len(cycle)<4 or any(sum(adjacent(u,v) for v in cycle)!=2 for u in cycle):
                        raise ValueError("Invalid cycle cut")
            good={tuple(q["prefix"]) for q in row["queries"].values() if q["status"]=="excluded"}
            steps={1<<j for j in range(8)}-set(P[1:])
            roots[tag]="certified" if (0,) in good or all((0,v) in good for v in steps) else "open"
    focus=MS/"255-parity-exchange-arms/focus-closure.json"
    prior_replay=MS/"255-parity-exchange-arms/closure-replay.json"
    histories=load(focus)
    checked=load(prior_replay)
    details=checked["closures"]["focus"]
    if (not histories["closed"] or histories["pending"] or details["shapes"]!=len(paths)
            or set(details["per_source"])!=set(paths)
            or checked["pins"][focus.relative_to(MS).as_posix()]!=digest(focus)):
        raise ValueError("Unverified component enumeration")
    extended=[]
    for shape,path in paths.items():
        for seq in (path,path[::-1]):
            for axis in range(8):
                v=seq[-1]^(1<<axis)
                if v not in seq and not any(adjacent(v,u) for u in seq[:-1]): extended.append([shape,axis])
    complete=[s for s in paths if all(roots[s+":"+str(e)]!="open" for e in (0,1))]
    archive=MS/"254-distant-arm-partners/aggregate.json"
    w=max((r for r in load(archive)["cases"] if r["shape"] in paths),key=lambda r:r["joined_edges"])
    if (sha256(p.shape(w["parent"])).hexdigest()!=w["shape"] or len(w["parent"])!=97
            or w["joined"]!=w["parent"][::-1]+[v+256 for v in w["partner"]]
            or len(w["joined"])-1!=w["joined_edges"]):
        raise ValueError("Wrong archived construction")
    return dict(roots=roots,closed_shapes=sorted(complete),endpoint_extensions=extended,
        component_witness=dict(shape=w["shape"],edges=w["joined_edges"],pairs=bank.check_path(w["joined"],9),
            vertices=w["joined"]),closure_replay_sha256=digest(prior_replay),witness_source_sha256=digest(archive))

def expanded_words(original):
    records=load(MS/"248-rooted-arm-capacity/attainers.json")["records"]
    samples=[s["path"] for row in records for s in row["paths"]]
    for name in ("261-rerouted-partners/intervals.json","255-parity-exchange-arms/constructive.json"):
        samples.extend(r["partner"] for r in load(MS/name)["cases"].values())
    words={tuple(p) for p in original}
    for path in samples:
        for seq in (path,path[::-1]):
            for start in range(len(seq)-1):
                dims=[]
                values=[0]
                for u,v in zip(seq[start:],seq[start+1:]):
                    dim=u^v
                    if dim not in dims: dims.append(dim)
                    values.append(values[-1]^(1<<dims.index(dim)))
                words.add(tuple(values))
    return words

def rigid_path_exists(words,length,allowed):
    for prefix in {tuple(w[1:length+1]) for w in words if len(w)>length}:
        live=bank.ALL_MAPS
        for v in prefix:
            live &= allowed[v]
            if not live: break
        if live: return True
    return False

def check_family(r,words,parent,allowed,images):
    expected=parent[::-1]+[v+256 for v in r["partner"]]
    if expected!=r["joined"] or bank.check_path(expected,9)!=r["pairs"]: raise ValueError("Construction mismatch")
    best=r["free_odd_partner"]
    fam,count=reconstruct(best,words,allowed,images)
    if not count or (best<95 and reconstruct(best+1,words,allowed,images)!=(0,0)):
        raise ValueError("Maximum mismatch")
    rigid=r["rigid_partner"]
    if not rigid_path_exists(words,rigid,allowed) or rigid_path_exists(words,rigid+1,allowed):
        raise ValueError("Fixed-donor maximum mismatch")
    return dict(rigid=rigid,free_odd=best,joined_edges=r["joined_edges"],
        maximizing_even_orders=fam,distinct_labelled_maximum_partners=count)

def main():
    d=load(HERE/"constructions.json")
    wide=load(HERE/"expanded-constructions.json")
    words=[vertices(bytes.fromhex(w)) for w in load(MS/"260-donor-intersections/catalogue.json")["words"]]
    expanded=expanded_words(words)
    if len(expanded)!=wide["words"]: raise ValueError("Expanded donor words differ")
    paths=load(MS/"255-parity-exchange-arms/focus-closure.json")["paths"]
    images=list(bank.permutation_images())
    faces={}
    for tag,r in d["cases"].items():
        shape,end=tag.split(":")
        parent=rooted(paths[shape],int(end))
        allowed=bank.allowed_maps(parent,images)
        faces[tag]=check_family(r,words,parent,allowed,images)
        faces[tag]["expanded"]=check_family(wide["cases"][tag],expanded,parent,allowed,images)
        # Count intersections between each full 48-site donor side and the parent,
        # allowing any order of that side and any choice of the other parity.
        minimum=48
        for even_set in {tuple(sorted(p[2::2])) for p in words}:
            bins=columns(bank.ALL_MAPS ^ allowed[v] for v in even_set)
            live=bank.ALL_MAPS
            low=0
            for j in reversed(range(len(bins))):
                lower=live & ~bins[j]
                if lower: live=lower
                else:
                    live &= bins[j]
                    low |= 1<<j
            minimum=min(minimum,low)
        even_only=[mask if not v.bit_count()%2 else bank.ALL_MAPS for v,mask in enumerate(allowed)]
        checked,hits=census(sorted(bytes.fromhex(w) for w in load(MS/"260-donor-intersections/catalogue.json")["words"]),even_only,minimum)
        if checked!=minimum or not hits: raise ValueError("Even-site minimum mismatch")
        word,rank=hits[0]
        collisions=sorted({images[rank][v] for v in vertices(bytes.fromhex(word))[2::2]} & set(parent[1:]))
        if len(collisions)!=minimum: raise ValueError("Wrong minimizing placement")
        faces[tag].update(minimum_even_sites_to_change=minimum,minimizers=len(hits),
            example=dict(word=word,rank=rank,collisions=collisions))
    summary=global_coverage()
    summary.update(constructions=faces,expanded_words=len(expanded),inputs={f.name:digest(f) for f in (HERE/"endpoints.json",HERE/"constructions.json",HERE/"expanded-constructions.json",HERE/"repair.py",HERE/"endpoints.py",HERE/"audit.py")})
    proof_paths={q["proof"] for r in load(HERE/"endpoints.json")["cases"].values() for q in r["queries"].values() if q["status"]=="excluded"}
    if proof_paths!={p.relative_to(HERE).as_posix() for p in (HERE/"proofs").glob("*.gz")}: raise ValueError("Incomplete proof archive")
    summary["new_certificates"]=len(proof_paths)
    save(HERE/"summary.json",summary)
    print(Counter(summary["roots"].values()),len(summary["closed_shapes"]),summary["endpoint_extensions"])
    print("minimum omissions",Counter(r["minimum_even_sites_to_change"] for r in faces.values()))
    print("maximums",[(k[:8]+k[-2:],r["rigid"],r["free_odd"],r["distinct_labelled_maximum_partners"]) for k,r in faces.items()])

if __name__=="__main__": main()
