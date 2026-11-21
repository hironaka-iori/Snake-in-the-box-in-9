"""Construct and verify rooted partners by bank placement, local repair and tail growth."""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path
from random import Random
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
LAST = BASE / "251-eighty-edge-segments"
sys.path.insert(0, str(LAST))
import bank_capacity as bank

ALL = (1 << 256) - 1
NEIGHBOURS = [sum(1 << (v ^ (1 << i)) for i in range(8)) for v in range(256)]


def read(path):
    return json.loads(path.read_bytes())


def path_mask(path):
    return sum(1 << v for v in path)


def relabel(path):
    axes = {}
    result = [0]
    for u, v in zip(path, path[1:]):
        result.append(result[-1] ^ (1 << axes.setdefault(u ^ v, len(axes))))
    return bytes(result)


def near_maps(word, allowed):
    # Each bit represents one coordinate permutation. Track placements with
    # exactly 0, 1, or 2 collisions with this parent, over the whole seed.
    exact, one, two = bank.ALL_MAPS, 0, 0
    longest, first_rank = 0, 0
    for i, v in enumerate(word[1:], 1):
        usable = allowed[v]
        two = (two & usable) | (one & ~usable)
        one = (one & usable) | (exact & ~usable)
        exact &= usable
        if exact:
            longest, first_rank = i, (exact & -exact).bit_length()-1
        if not (exact | one | two):
            break
    return longest, first_rank, (exact, one, two)


def repair(path, forbidden, rng, quota):
    """Keep both outside portions; search replacement bridges in a bounded window."""
    hits = [i for i, v in enumerate(path) if (1 << v) & forbidden]
    if not hits or hits[-1] - hits[0] > 18:
        return None
    for margin in (1, 2, 3):
        a = max(0, hits[0]-margin)
        b = min(len(path)-1, hits[-1]+margin)
        if a in hits or b in hits or b-a < 2:
            continue
        fixed = path[:a+1] + path[b:]
        left, right = fixed[a], path[b]
        # Future interior vertices avoid all fixed non-anchors and their
        # neighbours. The first and final bridge vertices may touch an anchor.
        free = ALL & ~(forbidden | path_mask(fixed))
        for v in path[:a]+path[b+1:]:
            free &= ~NEIGHBOURS[v]
        for length in (b-a+2,b-a,b-a-2):
            if length < 2: continue
            steps = [left]
            remaining_nodes = quota
            def extend(available):
                nonlocal remaining_nodes
                remaining_nodes -= 1
                v = steps[-1]
                left_steps = length-len(steps)+1
                if left_steps == 1:
                    if (v ^ right).bit_count() == 1:
                        return path[:a] + steps + path[b:]
                    return None
                options = NEIGHBOURS[v] & available
                if left_steps != 2:
                    options &= ~NEIGHBOURS[right]
                children = []
                while options:
                    bit = options & -options
                    options -= bit
                    u = bit.bit_length()-1
                    h = (right ^ u).bit_count()
                    if h <= left_steps-1:
                        children.append((h,rng.random(),u))
                for _,__,u in sorted(children):
                    if remaining_nodes <= 0: break
                    steps.append(u)
                    found = extend(available & ~(NEIGHBOURS[v] | (1 << v)))
                    steps.pop()
                    if found: return found
                return None
            fixed_path = extend(free)
            if fixed_path: return fixed_path
    return None


def tail_search(parent, initial, rng):
    best = list(initial)
    for attempt in range(84):
        # A slice is an induced initial path. Vary the retained fraction, keeping
        # long promising prefixes on most restarts; random choices break ties.
        cut = rng.randrange(1,len(best)+1) if attempt%4==0 else rng.randrange(max(1,len(best)//2), len(best)+1)
        stack = best[:cut]
        free = ALL & ~path_mask(parent)
        for v in stack[:-1]:
            free &= ~(NEIGHBOURS[v] | (1 << v))
        quota = 2400
        def grow(available):
            nonlocal quota, best
            quota -= 1
            tip = stack[-1]
            moves = NEIGHBOURS[tip] & available
            if len(stack)>len(best): best=stack.copy()
            after = available & ~(NEIGHBOURS[tip] | (1 << tip))
            choices = []
            while moves:
                bit=moves & -moves
                moves-=bit
                v=bit.bit_length()-1
                degree = (NEIGHBOURS[v] & after).bit_count() if attempt%3 else 0
                choices.append((degree,rng.random(),v))
            for _,__,v in sorted(choices):
                if quota<=0: break
                stack.append(v); grow(after); stack.pop()
        grow(free)
    return best


def check_join(parent, partner):
    joined = parent[::-1] + [256 + v for v in partner]
    if partner[0] != 0 or set(parent).intersection(partner) != {0}:
        raise ValueError("Partner intersects the parent away from the joining vertex")
    return dict(partner=partner,joined=joined,partner_edges=len(partner)-1,joined_edges=len(joined)-1,
                all_pairs={k:bank.check_path(p,d) for k,p,d in
                           (("parent",parent,8),("partner",partner,8),("joined",joined,9))})


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--core",type=int,default=68)
    cli.add_argument("--start",type=int,default=0,help="zero-based index in the census new_shapes array")
    cli.add_argument("--count",type=int,default=100000)
    args=cli.parse_args()
    census=HERE/f"census-{args.core}.json"
    archive=BASE/"248-rooted-arm-capacity"/"attainers.json"
    last_witnesses=LAST/"regrowth-witnesses.json"
    inputs=[census,archive,last_witnesses,bank.DONORS,Path(bank.__file__),Path(__file__)]
    pins={p.relative_to(BASE).as_posix():sha256(p.read_bytes()).hexdigest() for p in inputs}
    donors=[r["path"] for r in read(bank.DONORS)["shapes"]]
    words, reps=bank.donor_suffixes(donors)
    images=list(bank.permutation_images())
    seeds=[w["path"] for r in read(archive)["records"] for w in r["paths"]]
    seeds += [r["partner"] for r in read(last_witnesses)["cases"]]
    for p in seeds: bank.check_path(p,8)
    library=sorted({relabel(q) for p in seeds for q in (p,p[::-1])})
    rows=read(census)["new_shapes"]
    ledger=HERE/f"construct-{args.core}.json"
    data=read(ledger) if ledger.exists() else dict(pins=pins, donor_count=len(donors),seed_classes=len(library),cases=[])
    if data["pins"]!=pins: raise ValueError("Construction input hashes differ")
    if args.start<0 or args.count<1: raise ValueError("Invalid batch indices")
    done={(r["id"],r["end"]) for r in data["cases"]}
    for index in range(args.start,min(len(rows),args.start+args.count)):
        row=rows[index]
        for end, order in enumerate((row["path"],row["path"][::-1])):
            if (row["id"],end) in done: continue
            parent=[v^order[0] for v in order]
            rng=Random(int(row["id"][:16],16)*2+end)
            allowed=bank.allowed_maps(parent,images)
            fit=bank.longest(words,allowed)
            donor=bank.make_witness(donors,reps[fit[1]],fit,parent)
            exclusion=bank.exclude_next(donors,words,allowed,fit[0]+1)
            initial=donor["partner"]
            forbidden=path_mask(parent[1:])
            repairs=[]
            for word in library:
                length, rank, levels=near_maps(word,allowed)
                if length>=len(initial):
                    initial=list(word[:length+1].translate(images[rank]))
                for count,maps in enumerate(levels[1:],1):
                    for _ in range(8):
                        if not maps: break
                        bit=maps & -maps; maps-=bit
                        q=list(word.translate(images[bit.bit_length()-1]))
                        hits=[i for i,v in enumerate(q) if forbidden & (1<<v)]
                        if len(hits)!=count: raise ValueError("Incorrect overlap classification")
                        if hits[-1]-hits[0]<=18:
                            repairs.append((-len(q),len(hits),hits[-1]-hits[0],q))
            before=len(initial)-1
            for _,__,___,q in sorted(repairs)[:48]:
                candidate=repair(q,forbidden,rng,350)
                if candidate and len(candidate)>len(initial):
                    check_join(parent,candidate)
                    initial=candidate
            improved=tail_search(parent,initial,rng)
            best=check_join(parent,improved)
            result=dict(id=row["id"],end=end,root=order[0],edges=row["edges"],bank_fit=donor,
                        next_donor_length_excluded=exclusion,initial_prefix=before,after_repair=len(initial)-1,
                        **best)
            data["cases"].append(result)
            temp=ledger.with_suffix(".tmp")
            temp.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
            temp.replace(ledger)
            print(index,end,"donor",fit[0],"seed",before,"repair",len(initial)-1,"join",best["joined_edges"],flush=True)


if __name__=="__main__": main()
