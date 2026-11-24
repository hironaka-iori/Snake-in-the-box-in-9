"""Check 95-edge partners at the endpoints of the 41-shape one-site exchange component."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0, str(MS / "263-distant-family-certificates"))
import family
from family import bank, load, save, digest, p


def evidence():
    focus = MS / "255-parity-exchange-arms/focus-closure.json"
    paths = load(focus)["paths"]
    old, files = family.sources()
    replay = MS / "263-distant-family-certificates/summary.json"
    parents = MS / "260-donor-intersections/catalogue.json"
    checked = load(replay)
    for file, expected in checked["inputs"].items():
        if digest(MS / file) != expected:
            raise ValueError("Changed Round 263 dependency: " + file)
    masks = {tag: mask for area in family.groups().values() for tag, mask in area.items()}
    for tag, root in checked["roots"].items():
        if root["complete"]:
            old["263/" + tag] = masks[tag]
    return paths, old, files + [focus, parents, replay]


def rooted(path, end):
    order = path[::-1] if end else path
    return [v ^ order[0] for v in order]


def rooted_axes(mask):
    rest = set(mask)
    u = 0
    axes = []
    word = []
    while rest:
        steps = [d for d in range(8) if u ^ (1 << d) in rest]
        if len(steps) != 1:
            raise ValueError("Source is not a rooted path")
        d, = steps
        if d not in axes:
            axes.append(d)
        word.append(axes.index(d))
        u ^= 1 << d
        rest.remove(u)
    return word, axes


def certificate_sources(paths, old, images):
    import runpy
    placements = runpy.run_path(str(MS / '262-common-forbidden-sites/transfer.py'))['placements']
    words = {name: rooted_axes(mask) for name,mask in old.items() if len(mask)==96}
    direct = {}
    for shape, path in sorted(paths.items()):
        if len(path) != 97 or bank.check_path(path, 8) != 4656:
            raise ValueError("Incorrect parent")
        for end in (0, 1):
            parent = set(rooted(path, end)[1:])
            key = shape + ":" + str(end)
            for name, mask in old.items():
                if mask <= parent:
                    direct[key] = dict(source=name, rank=0)
                    break
            if key not in direct:
                # Equal-size rooted paths are isometric iff their canonical rooted
                # transition words agree. The smaller core uses a permutation search.
                v, b = rooted_axes(parent)
                for name, mask in old.items():
                    if len(mask) != 96:
                        allowed = placements(mask, parent, images)
                        if allowed:
                            direct[key] = dict(source=name, rank=allowed[0])
                            break
                    else:
                        w, a = words[name]
                        if w == v:
                            perm = [b[a.index(i)] if i in a else None for i in range(8)]
                            if None in perm:
                                raise ValueError("Unused direction")
                            from itertools import permutations
                            rank = next(i for i,q in enumerate(permutations(range(8))) if list(q)==perm)
                            direct[key] = dict(source=name, rank=rank)
                            break
            if key in direct:
                row = direct[key]
                if not {images[row["rank"]][v] for v in old[row["source"]]} <= parent:
                    raise ValueError("Invalid transfer")
    return direct


def run():
    parser = ArgumentParser()
    parser.add_argument("seconds", type=float)
    parser.add_argument("--split", action="store_true")
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    paths, old, files = evidence()
    images = list(bank.permutation_images())
    direct = certificate_sources(paths, old, images)
    pins = {f.relative_to(MS).as_posix():digest(f) for f in files}
    result_file = HERE / "endpoints.json"
    data = load(result_file) if result_file.exists() else dict(inputs=pins, inherited=direct, cases={})
    if pins != data["inputs"] or direct != data["inherited"]:
        raise ValueError("Endpoint catalogue changed")
    print("Transferred roots",len(direct),"of",2*len(paths),flush=True)
    with TemporaryDirectory() as d:
        tmp=Path(d)
        tools=family.compilers(tmp)
        for shape,path in sorted(paths.items()):
            for end in (0,1):
                key=shape+":"+str(end)
                if key in direct: continue
                parent=rooted(path,end)
                F=set(parent[1:])
                blocked,extra,_,cuts,build=family.setup([key],{key:F},old,images)
                if any(not rule["sites"] for rule in cuts): raise ValueError("Unreported containment")
                entry=data["cases"].setdefault(key,dict(parent=parent,cuts=cuts,queries={}))
                if entry["parent"]!=parent or cuts!=entry["cuts"]: raise ValueError("Changed cuts")
                rows=entry["queries"]
                if args.replay:
                    for q in rows.values(): family.replay(HERE,tmp,tools[0],q,builder=build)
                    continue
                if rows.get("0",{}).get("status") in ("witness","excluded"): continue
                prefixes=[[0,v] for v in p.joins.partner.next_vertices([0]+sorted(F),[0])] if args.split else [[0]]
                for prefix in prefixes:
                    label=",".join(map(str,prefix))
                    prev=rows.get(label)
                    if prev and prev["status"] in ("witness","excluded"): continue
                    q=family.query(HERE,tmp,tools,F,args.seconds,extra,prefix,prev,builder=build)
                    rows[label]=q
                    save(result_file,data)
                    print(key[:8],end,prefix,q["status"],len(cuts),flush=True)
                    if q["status"]=="witness":
                        seq=parent[::-1]+[256+v for v in q["path"]]
                        save(HERE/"candidate-192.json",dict(vertices=seq,edges=len(seq)-1,pairs=bank.check_path(seq,9)))
                        return
    if not args.replay: save(result_file,data)

if __name__=="__main__": run()
