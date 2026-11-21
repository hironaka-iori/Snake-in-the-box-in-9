"""Transport archived partners into the four additional parity-family parents, then regrow."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
from random import Random
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
MS = HERE.parent
PRIOR = MS / "253-repeated-segment-growth"
sys.path.insert(0, str(PRIOR))
import remote_arms as previous
from construct254 import COMPILER, SOURCE

search = previous.search
RESULT = HERE / "parity-joins.json"
FAMILY = HERE / "parity-families.json"
OPTIMA = HERE / "constructive.json"
BASELINE = PRIOR / "remote-arms.json"
OLD = MS / "252-shorter-reference-segments" / "construct-68.json"
ARCHIVE = MS / "248-rooted-arm-capacity" / "attainers.json"


def catalogue():
    data = search.read(OPTIMA)["cases"]
    current = [(OPTIMA, label, row["partner"]) for label, row in data.items()]
    rows = list(current)
    for file in (BASELINE, OLD):
        rows.extend((file,r["id"]+":"+str(r["end"]),r["partner"]) for r in search.read(file)["cases"])
    for label, r in data.items():
        for p in r["prefixes"]:
            rows.append((OPTIMA, label + ":prefix" + str(p["frozen_edges"]), p["partner"]))
    for r in search.read(ARCHIVE)["records"]:
        rows.extend((ARCHIVE,str(r["class_id"])+":"+str(i),p["path"]) for i,p in enumerate(r["paths"]))
    for label, arm in search.read(FAMILY)["shapes"].items():
        rows.append((FAMILY, label, arm))
    library = {}
    for file, label, arm in rows:
        search.bank.check_path(arm, 8)
        for end, order in enumerate((arm,arm[::-1])):
            word = search.relabel(order)
            library.setdefault(word, dict(file=file.name, arm=label, end=end))
    return current, rows, library


def placed(rooted, library, current, images):
    forbidden = search.path_mask(rooted[1:])
    allowed = search.bank.allowed_maps(rooted, images)
    candidates, near, exact = {}, [], {}
    totals = Counter()
    rng = Random(int.from_bytes(bytes(rooted), "big"))

    def store(vertices, origin):
        candidates.setdefault(bytes(vertices), origin)

    longest_len, longest_source = -1, None
    for word, origin in library.items():
        length, rank, levels = previous.full_maps(word, allowed)
        where = dict(**origin, permutation_rank=rank)
        prefix = word[:length+1].translate(images[rank])
        store(prefix, dict(method="placed_prefix", **where))
        if length > longest_len:
            longest_len, longest_source = length, where
        exact[word] = (length,rank,levels[0].bit_count())
        for collisions, mask in enumerate(levels):
            totals[collisions] += mask.bit_count()
            for slot in range(6):
                if not mask:
                    break
                bit = mask & -mask
                mask -= bit
                chosen = bit.bit_length()-1
                arm = word.translate(images[chosen])
                origin_rank = dict(**origin, permutation_rank=chosen)
                if collisions == 0:
                    store(arm, dict(method="complete_placement", **origin_rank))
                    continue
                hits = [j for j,x in enumerate(arm) if (1<<x)&forbidden]
                if len(hits)!=collisions: raise ValueError("Wrong full collision class")
                near.append((arm,hits,origin_rank))
    # Consider long near-misses, then near-misses requiring very few changes.
    length_order = sorted(near, key=lambda t:(-len(t[0]),len(t[1]),t[1][-1]-t[1][0],t[0]))
    collision_order = sorted(near, key=lambda t:(len(t[1]),-len(t[0]),t[1][-1]-t[1][0],t[0]))
    tried = set()
    for pair in zip(length_order,collision_order):
        for q,hits,origin in pair:
            if q in tried: continue
            tried.add(q)
            repaired = previous.repair_clusters(list(q), forbidden, rng)
            if len(repaired) > 1:
                store(repaired, dict(method="repair", input_collision_positions=hits, **origin))
        if len(tried)>=160: break
    originals = {}
    for _,label,q in current:
        originals[label] = []
        for end,order in enumerate((q,q[::-1])):
            plen,rank,count = exact[search.relabel(order)]
            originals[label].append(dict(end=end, longest_prefix=plen,
                                         prefix_permutation_rank=rank, complete_placements=count))
    complete_max = max((len(word)-1 for word,item in exact.items() if item[2]),default=None)
    stats = dict(exhaustive_maximum_prefix=longest_len, prefix_attainer=longest_source,
                 exhaustive_longest_complete_seed=complete_max, complete_collision_counts=dict(totals),
                 four_previous_best=originals, repair_candidates=len(tried))
    leaders = sorted(candidates,key=lambda p:(-len(p),p))
    distinct = []
    for p in leaders:
        if len(p)<len(leaders[0])-5: break
        if any(len(set(p)^set(q))<4 for q in distinct): continue
        distinct.append(p)
        if len(distinct)==4: break
    return [(list(p),candidates[p]) for p in distinct],stats


def grow(exe, rooted, seeds, salt):
    best = max((p for p,_ in seeds), key=len)
    attempts = []
    for index,(arm,origin) in enumerate(seeds):
        search.check_join(rooted,arm)
        data = "".join(",".join(map(str,p))+"\n" for p in (rooted,arm))
        lines = subprocess.run([str(exe),str(salt+index)], input=data,text=True,capture_output=True,
                               check=True,timeout=150).stdout.splitlines()
        fields = lines[-1].split()
        if fields[0] != "regrowth": raise ValueError("Incomplete native regrowth")
        revised = [int(x) for x in fields[4].split(",")]
        search.check_join(rooted,revised)
        attempts.append(dict(seed=arm, origin=origin, random_seed=salt+index,
                             seed_edges=len(arm)-1, best_edges=len(revised)-1))
        if len(revised)>len(best): best=revised
    return best,attempts


def main():
    current, rows, library = catalogue()
    family = search.read(FAMILY)
    if len(family["outside_previous"]) != 4: raise ValueError("Unexpected number of new shapes")
    files = (FAMILY, OPTIMA, BASELINE, OLD, ARCHIVE, SOURCE, Path(__file__), HERE/"construct254.py",
             Path(previous.__file__), Path(search.__file__),Path(search.bank.__file__))
    pins = {p.relative_to(MS).as_posix():sha256(p.read_bytes()).hexdigest() for p in files}
    data = search.read(RESULT) if RESULT.exists() else dict(
        pins=pins, input_arms_by_file=Counter(p.name for p,_,_ in rows), distinct_directed_shapes=len(library),
        axis_permutations_per_shape=40320, cases={})
    if data["pins"]!=pins: raise ValueError("Inputs changed before completing this census")
    cases=[(key,end) for key in sorted(family["outside_previous"]) for end in (0,1)]
    keys=[key[:8]+"-"+str(end) for key,end in cases]
    if set(sys.argv[1:])-set(keys): raise ValueError("Unknown root")
    images=list(search.bank.permutation_images())
    with TemporaryDirectory() as tmp:
        exe=Path(tmp)/"PartnerGrowth.exe"
        subprocess.run([str(COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(SOURCE)],
                       check=True,capture_output=True)
        for index,((key,end),name) in enumerate(zip(cases,keys)):
            if sys.argv[1:] and name not in sys.argv[1:]: continue
            seq=family["shapes"][key]
            order=seq[::-1] if end else seq
            rooted=[v^order[0] for v in order]
            search.bank.check_path(rooted,8)
            seeds,stats=placed(rooted,library,current,images)
            best,attempts=grow(exe,rooted,seeds,254100+index*10)
            checked=search.check_join(rooted,best)
            data["cases"][name]=dict(id=key,end=end,root=order[0],parent_edges=len(rooted)-1,
                                    placement=stats,regrowth=attempts,**checked)
            tmpfile=RESULT.with_suffix(".tmp")
            tmpfile.write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8",newline="\n")
            tmpfile.replace(RESULT)
            print(name,order[0],stats["exhaustive_maximum_prefix"],len(seeds[0][0])-1,
                  checked["partner_edges"],checked["joined_edges"],flush=True)


if __name__=="__main__":
    main()
