"""Place every segment of saved partner paths at new endpoints and regrow the best placements."""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
MS = HERE.parent
PREVIOUS = MS / "254-distant-arm-partners"
sys.path.insert(0, str(PREVIOUS))
from construct254 import COMPILER, SOURCE, check_join
import construct

bank = construct.bank
ARMS = HERE / "arms.json"
RESULT = HERE / "constructive.json"


def read(path):
    return json.loads(path.read_bytes())


def save(data):
    temp = RESULT.with_suffix(".tmp")
    temp.write_text(json.dumps(data, separators=(",", ":"))+"\n", encoding="utf-8", newline="\n")
    temp.replace(RESULT)


def sources():
    rows = []
    files = [ARMS, Path(__file__), SOURCE, COMPILER, Path(construct.__file__), Path(bank.__file__),
             PREVIOUS / "construct254.py"]
    archive = MS / "248-rooted-arm-capacity" / "attainers.json"
    files.append(archive)
    for r in read(archive)["records"]:
        for i, sample in enumerate(r["paths"]):
            rows.append((archive.name, str(r["class_id"])+":"+str(i), sample["path"]))
    for name in ("aggregate","constructive","parity-joins","prefix-optima"):
        src = PREVIOUS / (name+".json")
        files.append(src)
        if name == "aggregate":
            for r in read(src)["cases"]:
                rows.append((src.name,r["shape"]+":"+str(r["root"]),r["partner"]))
        else:
            for label,r in sorted(read(src)["cases"].items()):
                rows.append((src.name,label,r["partner"]))
    # Every segment and axis map will be tried, so isometric or reversed donors suffice once.
    unique = {}
    for name,label,p in rows:
        bank.check_path(p,8)
        code = min(construct.relabel(p), construct.relabel(p[::-1]))
        unique.setdefault(code,(name,label,p))
    pins = {p.relative_to(MS).as_posix() if p.is_relative_to(MS) else p.name:
            sha256(p.read_bytes()).hexdigest() for p in files}
    return list(unique.values()), pins, len(rows)


def placements(parent, donors, groups, maps):
    allowed = bank.allowed_maps(parent,maps)
    choices = {}
    maxima = []
    for index, (words, descriptors) in enumerate(groups):
        fit = bank.longest(words,allowed)
        _, origin, direction = descriptors[fit[1]]
        witness = bank.make_witness(donors,(index,origin,direction),fit,parent)
        vertices = tuple(witness["partner"])
        description = {k:witness[k] for k in ("donor_index","donor_start","donor_step","donor_axes_image")}
        choices.setdefault(vertices, description)
        maxima.append(fit[0])
    leaders = sorted(choices,key=lambda p:(-len(p),p))
    return [dict(partner=list(p),**choices[p]) for p in leaders], maxima


def improve(case, partner):
    witness = check_join(case["parent"],partner)
    if "partner" not in case or len(partner) > len(case["partner"]):
        case.update(witness)


def grow(exe, parent, seed, salt):
    text = "\n".join(",".join(map(str,arm)) for arm in (parent,seed))+"\n"
    lines = subprocess.run([str(exe),str(salt)],input=text,text=True,capture_output=True,
                           check=True,timeout=150).stdout.splitlines()
    stage, bridges, bridge_nodes, tail_nodes, raw = lines[-1].split()
    if stage != "regrowth":
        raise ValueError("Incomplete native regrowth")
    partner = [int(v) for v in raw.split(",")]
    check_join(parent,partner)
    if len(partner) < len(seed):
        raise ValueError("Growth lost the seed")
    return dict(salt=salt, bridges=int(bridges), bridge_nodes=int(bridge_nodes),
                tail_nodes=int(tail_nodes), partner=partner)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--shapes",nargs="+",help="prefixes of the four new shape IDs")
    parser.add_argument("--ends",nargs="+",type=int,choices=(0,1),default=[0,1])
    parser.add_argument("--grow",type=int,default=1,help="distinct placed seeds per chosen endpoint, 0 for placement only")
    parser.add_argument("--transfer",action="store_true",help="also place all segments of current winners across all saved cases")
    args = parser.parse_args()
    if args.grow < 0:
        parser.error("growth count must be nonnegative")
    arms = read(ARMS)
    keys = sorted(arms["outside_previous"])
    chosen = keys
    if args.shapes:
        chosen = []
        for prefix in args.shapes:
            matched = [k for k in keys if k.startswith(prefix)]
            if len(matched)!=1:
                parser.error("unknown or ambiguous new shape "+prefix)
            if matched[0] not in chosen:
                chosen.append(matched[0])
    archive,pins,total = sources()
    donors = [p for _,_,p in archive]
    data = read(RESULT) if RESULT.exists() else dict(pins=pins,source_records=total,
            distinct_shapes=len(donors),donors=[dict(file=f,record=k,vertices=p) for f,k,p in archive],
            axis_permutations=40320,cases={})
    if data["pins"] != pins:
        raise ValueError("Construction inputs changed")
    groups = [bank.donor_suffixes([p]) for p in donors]
    maps = list(bank.permutation_images())
    selected = []
    for key in chosen:
        seq = arms["shapes"][key]
        for end in sorted(set(args.ends)):
            tag = key+":"+str(end)
            selected.append(tag)
            if tag in data["cases"]:
                continue
            order = seq[::-1] if end else seq
            parent = [v^order[0] for v in order]
            seeds,maxima = placements(parent,donors,groups,maps)
            case = dict(id=key,end=end,root=order[0],parent=parent,seeds=seeds,
                        donor_maxima=maxima,maximum_segment=max(maxima),growth=[])
            improve(case,seeds[0]["partner"])
            data["cases"][tag] = case
            save(data)
            print(key[:8],end,"placement",case["partner_edges"],flush=True)
    if args.grow:
        with TemporaryDirectory(prefix="snake255-partner-construct-") as tmp:
            exe = Path(tmp) / "PartnerGrowth.exe"
            subprocess.run([str(COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(SOURCE)],
                           check=True,capture_output=True,timeout=45)
            for tag in selected:
                case = data["cases"][tag]
                done = {item["placement_rank"] for item in case["growth"]}
                for i, seed in enumerate(case["seeds"][:args.grow]):
                    if i in done:
                        continue
                    salt = 255000 + 1000*keys.index(case["id"]) + 100*case["end"] + i
                    result = grow(exe,case["parent"],seed["partner"],salt)
                    improve(case,result["partner"])
                    case["growth"].append(dict(placement_rank=i,**result))
                    save(data)
                    print(case["id"][:8],case["end"],"growth",i,case["partner_edges"],flush=True)
    if args.transfer:
        # Freeze donor paths for the whole pass. This makes all shared-endpoint transfers symmetric.
        pool = [r["partner"] for _,r in sorted(data["cases"].items())]
        descriptions = [bank.donor_suffixes([p]) for p in pool]
        for tag in selected:
            case = data["cases"][tag]
            seeds,maxima = placements(case["parent"],pool,descriptions,maps)
            attained = seeds[0]
            improve(case,attained["partner"])
            transfer = dict(donor=pool[attained["donor_index"]], placed=attained, maximum_segment=max(maxima))
            case.setdefault("transfers",[])
            if transfer not in case["transfers"]:
                case["transfers"].append(transfer)
            save(data)
            print(case["id"][:8],case["end"],"transfer",case["partner_edges"],flush=True)


if __name__ == "__main__":
    main()
