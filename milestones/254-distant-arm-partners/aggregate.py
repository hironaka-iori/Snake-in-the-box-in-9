"""Reconcile rooted partner bounds, direct witnesses, prefix covers, and actual cube paths."""
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"251-eighty-edge-segments"))
import bank_capacity as bank
from family import root_family, file_hash, read, require, path_ok


def main():
    shapes=read(HERE/"parity-families.json")["shapes"]
    roots=sorted({v for p in shapes.values() for v in (p[0],p[-1])})
    caps={(k,v):[(98,"Q8")] for k,p in shapes.items() for v in (p[0],p[-1])}
    records=[];pins={}
    def load(name):
        f=HERE/name;pins[name]=file_hash(f);return read(f)
    def collect(p):
        path_ok(p,8);records.append(p)
    for name in ("constructive.json","parity-joins.json","prefix-optima.json"):
        for item in load(name)["cases"].values():
            p=item["partner"];k=item["id"];root=item["root"];parents,_,_=root_family(shapes,root)
            joined=parents[k][::-1]+[v+256 for v in p]
            require(joined==item["joined"] and item["partner_edges"]==len(p)-1 and len(joined)-1==item["joined_edges"],
                    "Construction metadata disagree")
            path_ok(joined,9);collect(p)
    archive=HERE.parent/"253-repeated-segment-growth"/"placements.json"
    pins[archive.relative_to(HERE.parent).as_posix()]=file_hash(archive)
    for entry in read(archive)["cases"]:
        if entry["id"] in shapes:
            for placed in entry["banks"].values():collect(placed["partner"])
    for name,checked in (("sat-caps.json","sat-replay.json"),("sibling-caps.json","sibling-replay.json")):
        data=load(name);replay=load(checked)
        require(replay["ledger_sha256"]==pins[name],"Stale fixed replay")
        for row in replay["roots"]:
            r=data["roots"][row["tag"]];cap=row["upper"];key=r["id"],r["root"]
            require(key in caps and cap==r["upper"],"Rooted bound mismatch")
            caps[key].append((cap,name))
            for item in r["attempts"]:
                if item["status"]=="witness":collect(item["partner"])
    blocked={}
    for name,checked in (("family-caps.json","family-replay.json"),("cut-caps.json","cut-replay.json")):
        data=load(name);replay=load(checked)
        require(replay["ledger"]==pins[name],"Stale family replay")
        for label,row in data["roots"].items():
            root=int(label);parents,common,_=root_family(shapes,root)
            if name.startswith("family"):
                sets=row["attempts"]
            else:sets={n:r["cases"] for n,r in row.items()}
            for target,entries in sets.items():
                n=int(target)
                for step,case in entries.items():
                    if case["status"]=="excluded":
                        blocked.setdefault((root,n),set()).add(int(step))
                    elif case["status"]=="witness":
                        p=case["partner"]
                        good=[k for k,v in parents.items() if set(v)&set(p)=={0}]
                        require(bool(good) and good==case["compatible_shapes"] and p[:len(case["prefix"])]==case["prefix"]
                                and len(p)==n+1,"Empty or invalid witnessed family")
                        for k in good:path_ok(parents[k][::-1]+[v+256 for v in p],9)
                        collect(p)
            cap=replay["roots"][label]["partner_upper"]
            for k in parents:caps[k,root].append((cap,name))
    for (root,n),closed in blocked.items():
        parents,common,_=root_family(shapes,root)
        steps={1<<i for i in range(8) if 1<<i not in common}
        if 0 in closed or steps<=closed:
            for k in parents:caps[k,root].append((n-1,"replayed family prefix cover"))
    for filename,replay_name,field in (("individual-caps.json","individual-replay.json","cases"),
                                       ("forced-caps.json","forced-replay.json","attempts")):
        data=load(filename); replay=load(replay_name)
        require(replay["ledger"]==pins[filename],"Stale individual replay")
        for tag,entries in data[field].items():
            k,v=tag.split(":");root=int(v)
            for t,r in entries.items():
                if r["status"] in ("excluded","inherited"):caps[k,root].append((int(t)-1,filename))
                if r["status"]=="witness":
                    q=r["partner"];p=root_family(shapes,root)[0][k]
                    require(q[0]==0 and len(q)==int(t)+1,"Incorrect positive root or length")
                    path_ok(p[::-1]+[v+256 for v in q],9);collect(q)
    maps=list(bank.permutation_images());words,descriptors=bank.donor_suffixes(records)
    results=[]
    for root in roots:
        parents,_,_=root_family(shapes,root)
        for k,p in sorted(parents.items()):
            allowed=bank.allowed_maps(p,maps);fit=bank.longest(words,allowed)
            lower=bank.make_witness(records,descriptors[fit[1]],fit,p)
            verify=bank.check_path(lower["joined"],9);require(verify==lower["all_pairs"]["joined"],"Pair count differs")
            upper,source=min(caps[k,root])
            require(lower["joined_edges"]<=97+upper,"Lower bound exceeds upper")
            results.append(dict(shape=k,root=root,partner_upper=upper,upper_source=source,**lower))
    pins["parity-families.json"]=file_hash(HERE/"parity-families.json")
    pins["aggregate.py"]=file_hash(Path(__file__));pins["bank_capacity.py"]=file_hash(Path(bank.__file__))
    report=dict(pins=pins,cases=results,undecided_192=[dict(shape=r["shape"],root=r["root"]) for r in results if r["partner_upper"]>=95],
        family_join_lower=max(r["joined_edges"] for r in results),family_join_upper=max(r["partner_upper"]+97 for r in results))
    (HERE/"aggregate.json").write_text(json.dumps(report,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print([(r["shape"][:8],r["root"],r["partner_edges"],r["partner_upper"]) for r in results])
    print("Family maximum interval",report["family_join_lower"],report["family_join_upper"])


if __name__=="__main__":main()
