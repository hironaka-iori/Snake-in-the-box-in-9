"""Exact single-crossing joins for two named finite opposite-arm banks."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE / "251-eighty-edge-segments"))
import bank_capacity as bank


def read(path):
    return json.loads(path.read_bytes())


def signature(path):
    """Coordinate names, initial translation and direction are immaterial."""
    steps = bytes((u ^ v).bit_length()-1 for u, v in zip(path, path[1:]))
    def standard(word):
        axes = bytes(dict.fromkeys(word))
        return word.translate(bytes.maketrans(axes,bytes(range(len(axes)))))
    return min(standard(steps),standard(steps[::-1]))


def partner_paths(tree, loc=()):
    if isinstance(tree, list):
        for i, item in enumerate(tree):
            if isinstance(item, (list, dict)):
                yield from partner_paths(item, loc+(i,))
    elif isinstance(tree, dict):
        for key, item in tree.items():
            if key == "partner" and isinstance(item, list) and len(item)>=91:
                if all(isinstance(v, int) for v in item):
                    yield list(loc+(key,)), item
            elif isinstance(item,(list,dict)):
                yield from partner_paths(item,loc+(key,))


def build_banks(closure, extra_sources):
    groups = {"closure": {}, "archive": {}}
    def add(group, path, location):
        bank.check_path(path,8)
        group.setdefault(signature(path),(location,path))
    for key, path in closure["paths"].items():
        add(groups["closure"],path,["closure.json","paths",key])
    for i, row in enumerate(read(bank.DONORS)["shapes"]):
        add(groups["archive"],row["path"],[bank.DONORS.relative_to(BASE).as_posix(),"shapes",i,"path"])
    for path in extra_sources:
        source = path.relative_to(BASE).as_posix()
        data = read(path)
        if path.name == "attainers.json":
            for i, row in enumerate(data["records"]):
                for j, entry in enumerate(row["paths"]):
                    add(groups["archive"],entry["path"],[source,"records",i,"paths",j,"path"])
        for loc, p in partner_paths(data):
            add(groups["archive"],p,[source,*loc])
    result = {}
    for name, group in groups.items():
        locations,paths = zip(*(group[k] for k in sorted(group)))
        words,descriptors = bank.donor_suffixes(paths)
        result[name]=(paths,locations,words,descriptors,{})
    return result


def impossible_next(words, cache, allowed, length):
    # The second enumeration ignores the sorted-suffix pruning of longest().
    # At the first impossible length, every distinct ordered segment is
    # independently checked against all physical coordinate placements.
    if length not in cache:
        unique=sorted({w[:length] for w in words if len(w)>=length})
        digest=sha256()
        vertices=[]
        for word in unique:
            v=0
            seq=bytearray()
            for axis in word:
                v ^= 1 << axis
                seq.append(v)
            vertices.append(bytes(reversed(seq)))
            digest.update(word)
        cache[length]=(digest.hexdigest(),vertices)
    digest,vertices=cache[length]
    for order in vertices:
        maps=bank.ALL_MAPS
        for v in order:
            maps &= allowed[v]
            if not maps: break
        if maps:
            raise ValueError("Next length admits a compatible placement")
    return dict(edges=length,distinct_rooted_words=len(vertices),axis_maps=bank.PERMUTATIONS,
                compatible_placements=0,words_sha256=digest)


def write(path, content):
    temporary=path.with_suffix(".tmp")
    temporary.write_text(json.dumps(content,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    temporary.replace(path)


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--start",type=int,default=0,help="first sorted new shape index")
    cli.add_argument("--count",type=int,default=10000)
    args=cli.parse_args()
    if args.start<0 or args.count<=0: raise ValueError("Invalid batch range")
    prior=BASE/"252-shorter-reference-segments"/"census-68.json"
    source=HERE/"closure.json"
    extra=[BASE/"248-rooted-arm-capacity"/n for n in
           ("attainers.json","endpoint94.json","lower-witnesses.json","opposite.json")]
    extra+=[BASE/"249-long-parent-joins"/n for n in
            ("witnesses.json","partners-92.json","partners-93.json","partners-94.json","partners-95.json")]
    extra+=[BASE/"251-eighty-edge-segments"/n for n in ("profiles.json","regrowth-witnesses.json")]
    extra.append(BASE/"252-shorter-reference-segments"/"construct-68.json")
    inputs=[prior,source,Path(__file__),Path(bank.__file__),bank.DONORS,*extra]
    pins={p.relative_to(BASE).as_posix():sha256(p.read_bytes()).hexdigest() for p in inputs}
    closure=read(source)
    original=set(read(prior)["all_ids"])
    if not closure["closed"] or not original<=closure["paths"].keys():
        raise ValueError("Incomplete closure or missing inherited arm")
    new=sorted(closure["paths"].keys()-original)
    if len(new)!=174: raise ValueError("Unexpected number of newly reached shapes")
    groups=build_banks(closure,extra)
    images=list(bank.permutation_images())
    destination=HERE/"placements.json"
    data=read(destination) if destination.exists() else dict(
        pins=pins,shapes=new,banks={name:dict(shapes=len(g[0]),distinct_suffix_words=len(g[2]),
            source_shape_labels=g[1]) for name,g in groups.items()},cases=[])
    if data["pins"]!=pins or data["shapes"]!=new:
        raise ValueError("Saved placements belong to different inputs")
    done={(r["id"],r["end"]) for r in data["cases"]}
    for i in range(args.start,min(args.start+args.count,len(new))):
        key=new[i]
        p=closure["paths"][key]
        for end, order in enumerate((p,p[::-1])):
            if (key,end) in done: continue
            parent=[v^order[0] for v in order]
            allowed=bank.allowed_maps(parent,images)
            record=dict(id=key,end=end,root=order[0],parent_edges=len(parent)-1,banks={})
            for name,(paths,locations,words,descriptors,cache) in groups.items():
                best=bank.longest(words,allowed)
                witness=bank.make_witness(paths,descriptors[best[1]],best,parent)
                exclusion=impossible_next(words,cache,allowed,best[0]+1)
                record["banks"][name]=dict(
                    partner_edges=witness["partner_edges"],joined_edges=witness["joined_edges"],
                    donor=witness["donor_index"],start=witness["donor_start"],direction=witness["donor_step"],
                    axis_images=witness["donor_axes_image"],partner=witness["partner"],all_pairs=witness["all_pairs"],
                    next_length_exclusion=exclusion)
                if witness["joined_edges"]>=192:
                    write(HERE/f"witness-{i}-{end}-{name}.json",dict(id=key,end=end,**witness))
                    print("Verified",witness["joined_edges"],"edges",key,end,name,flush=True)
            data["cases"].append(record)
        if (i+1)%10==0:
            write(destination,data)
            print("Completed shape index",i,flush=True)
    data["summary"]=dict(roots=len(data["cases"]),expected=2*len(new),complete=len(data["cases"])==2*len(new),
        by_bank={name:dict(maximum_join=max((r["banks"][name]["joined_edges"] for r in data["cases"]),default=0),
                           join_histogram=Counter(r["banks"][name]["joined_edges"] for r in data["cases"]))
                 for name in groups})
    write(destination,data)
    print("Covered",len(data["cases"]),"roots.",{n:v["maximum_join"] for n,v in data["summary"]["by_bank"].items()})


if __name__=="__main__":
    main()
