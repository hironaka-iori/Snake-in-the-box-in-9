"""Choose the odd vertices of a partner afresh for an ordered sequence of even vertices."""
from functools import lru_cache
from pathlib import Path
from endpoints import HERE, MS, bank, rooted, digest, load, save
from census import vertices

N = [tuple(v ^ (1 << i) for i in range(8)) for v in range(256)]


@lru_cache(maxsize=4096)
def choices(evens, odd_end):
    # Each connector must see only its two intended neighbours in the even list.
    side = set(evens)
    clauses = []
    for u, v in zip(evens, evens[1:]):
        clauses.append(tuple(w for w in N[u] if set(N[w]) & side == {u, v}))
    if odd_end:
        clauses.append(tuple(w for w in N[evens[-1]] if set(N[w]) & side == {evens[-1]}))
    return clauses


def layouts(words, length):
    # Prefixes with the same ordered even vertices have the same expansions.
    return {tuple(seq[:length+1:2]): key for key, seq in words.items() if len(seq)>length}


def locate(words, length, allowed):
    for evens, key in layouts(words, length).items():
        maps = bank.ALL_MAPS
        for v in evens[1:]:
            maps &= allowed[v]
            if not maps: break
        if not maps: continue
        clauses = choices(evens, length % 2)
        for options in clauses:
            union = 0
            for v in options: union |= allowed[v]
            maps &= union
            if not maps: break
        if maps:
            rank = (maps & -maps).bit_length()-1
            partner = []
            for i,v in enumerate(evens):
                partner.append(v)
                if i < len(clauses):
                    partner.append(next(w for w in clauses[i] if (allowed[w] >> rank) & 1))
            return key, rank, partner
    return None


def donors(expanded):
    cat = MS / "260-donor-intersections/catalogue.json"
    words = {k:vertices(bytes.fromhex(k)) for k in load(cat)["words"]}
    sources=[cat]
    if expanded:
        samples=[]
        for path in (MS/"261-rerouted-partners/intervals.json",MS/"255-parity-exchange-arms/constructive.json"):
            samples.extend(row["partner"] for row in load(path)["cases"].values())
            sources.append(path)
        attaining=MS/"248-rooted-arm-capacity/attainers.json"
        samples.extend(w["path"] for row in load(attaining)["records"] for w in row["paths"])
        sources.append(attaining)
        suffixes,_=bank.donor_suffixes(samples)
        words.update({w.hex():vertices(w) for w in suffixes})
    return words,sources

def main():
    import sys
    expanded="--expanded" in sys.argv
    past = MS / "257-three-exchange-parents/summary.json"
    current = MS / "263-distant-family-certificates/summary.json"
    component = MS / "255-parity-exchange-arms/focus-closure.json"
    control = MS / "259-four-exchange-component/attaining-191.json"
    words,sources = donors(expanded)
    shapes = sorted(set(load(past)["remaining_in_41_shape_component"])-set(load(current)["newly_closed_shapes"]))
    paths = load(component)["paths"]
    images = list(bank.permutation_images())
    witness = load(control)
    if witness["parent"][::-1]+[v+256 for v in witness["partner"]] != witness["vertices"]:
        raise ValueError("Control orientation differs")
    control_path = witness["partner"]
    clauses = choices(tuple(control_path[::2]), (len(control_path)-1)%2)
    if any(v not in opts for v,opts in zip(control_path[1::2],clauses)) or bank.check_path(witness["vertices"],9)!=18336:
        raise ValueError("191-edge control did not survive contraction")
    cases = {}
    for shape in shapes:
        for end in (0,1):
            key = shape+":"+str(end)
            parent = rooted(paths[shape],end)
            allowed = bank.allowed_maps(parent,images)
            rigid, _, _ = bank.longest(sorted(bytes.fromhex(w) for w in words),allowed)
            lo,hi=rigid,96
            while hi-lo>1:
                mid=(lo+hi)//2
                if locate(words,mid,allowed): lo=mid
                else: hi=mid
            word,rank,preimage=locate(words,lo,allowed)
            placed=[images[rank][v] for v in preimage]
            joined=parent[::-1]+[v+256 for v in placed]
            if len(placed)!=lo+1 or set(parent)&set(placed)!={0}: raise ValueError("Invalid placement")
            cases[key]=dict(rigid_partner=rigid,free_odd_partner=lo,joined_edges=len(joined)-1,
                word=word,rank=rank,partner=placed,joined=joined,pairs=bank.check_path(joined,9))
            print(key[:8],end,rigid,lo,len(joined)-1,flush=True)
    output="expanded-constructions.json" if expanded else "constructions.json"
    save(HERE/output,dict(cases=cases,words=len(words),maps=len(images),control_pairs=18336,
        inputs={f.relative_to(MS).as_posix():digest(f) for f in [*sources,past,current,component,control,Path(__file__)]}))

if __name__=="__main__": main()
