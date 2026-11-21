"""Place every segment of the 72 generated partner shapes against the long-arm inventory."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0, str(MS / "251-eighty-edge-segments"))
import bank_capacity as bank


def load(path):
    return json.loads(path.read_bytes())


def main():
    pool = HERE / "partner-pool.json"
    extended = HERE / "focus-closure.json"
    old = MS / "253-repeated-segment-growth" / "closure.json"
    parity = MS / "254-distant-arm-partners" / "parity-families.json"
    arms = load(old)["paths"] | load(parity)["shapes"] | load(extended)["paths"]
    focus = set(load(extended)["paths"])
    attainers = set(load(HERE / "attainer-closure.json")["paths"])
    donor_ids, donors = zip(*sorted(load(pool)["shapes"].items()))
    if len(arms) != 264 or len(donors) != 72:
        raise ValueError("The placement scope differs")
    words, origins = bank.donor_suffixes(donors)
    images = list(bank.permutation_images())
    src = (pool, extended, old, parity, HERE/"attainer-closure.json", Path(bank.__file__), Path(__file__))
    pins = {p.relative_to(MS).as_posix():sha256(p.read_bytes()).hexdigest() for p in src}
    out = HERE / "pool-joins.json"
    d = load(out) if out.exists() else dict(pins=pins, donor_ids=donor_ids, cases={})
    if pins != d["pins"]:
        raise ValueError("Placement inputs changed")
    def save():
        tmp = out.with_suffix(".tmp")
        tmp.write_text(json.dumps(d,separators=(",",":"))+"\n", encoding="utf-8", newline="\n")
        tmp.replace(out)
    for i, (key, seq) in enumerate(sorted(arms.items(), key=lambda kv:(kv[0] not in focus | attainers,kv[0]))):
        for end, order in enumerate((seq,seq[::-1])):
            tag = key + ":" + str(end)
            if tag in d["cases"]:
                continue
            parent = [v ^ order[0] for v in order]
            allowed = bank.allowed_maps(parent,images)
            best = bank.longest(words,allowed)
            found = bank.make_witness(donors,origins[best[1]],best,parent)
            higher = bank.exclude_next(donors,words,allowed,best[0]+1)
            d["cases"][tag] = dict(shape=key,end=end,root=order[0], **found, exclusion=higher)
        if (i+1) % 20 == 0:
            print(i+1,"parents covered",flush=True)
            save()
    d["maxima"] = {}
    for label, ids in (("all",set(arms)),("five_attainers_closure",attainers),("round254_seed_closure",focus)):
        rows = [v for v in d["cases"].values() if v["shape"] in ids]
        longest = max(v["joined_edges"] for v in rows)
        d["maxima"][label] = dict(parents=len(ids),roots=len(rows), joined_edges=longest,
                                    attaining_roots=[[v["shape"],v["end"]] for v in rows if v["joined_edges"]==longest],
                                    histogram=Counter(v["joined_edges"] for v in rows))
    save()
    print({k:v["joined_edges"] for k,v in d["maxima"].items()})


if __name__ == "__main__":
    main()
