"""Place the long Q8 donors at every fixed root and count unavoidable cross-face chords."""
from collections import Counter
from pathlib import Path
from tempfile import TemporaryDirectory
import gzip
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0, str(MS / "267-fixed-arm-extensions"))
from donors import bank, physical, rename, read, write
from align import counter
from growth import CSC, checked
from hashlib import sha256


def library():
    raw = (MS / "267-fixed-arm-extensions/donor-paths.json.gz").read_bytes()
    assert sha256(raw).hexdigest() == read(MS / "267-fixed-arm-extensions/donors.json")["sha256"]
    return [bytes.fromhex(code) for code, _ in json.loads(gzip.decompress(raw))]


def segments(pool, minimum, maximum):
    words = {}
    for index, code in enumerate(pool):
        for direction, seq in ((1, code), (-1, code[::-1])):
            for i in range(len(seq) - minimum + 1):
                word = rename(seq[i:i + maximum])
                origin = i if direction == 1 else len(seq) - i
                words.setdefault(word, (index, origin, direction))
    return words


def minimum_overlap(words, allowed, images, parent):
    """Minimise by bit-sliced addition. Replay the lower bound by counting up to the minimum."""
    best, example = 257, None
    for w in words:
        seq = physical(w)[1:]
        bits = counter.columns(bank.ALL_MAPS ^ allowed[v] for v in seq)
        value, ties = 0, bank.ALL_MAPS
        for i in reversed(range(len(bits))):
            without = ties & ~bits[i]
            if without:
                ties = without
            else:
                value += 1 << i
        if value < best:
            rank = (ties & -ties).bit_length() - 1
            moved = list(physical(w).translate(images[rank]))
            hits = sorted(set(moved) & set(parent) - {0})
            assert len(hits) == value
            best, example = value, dict(word=w.hex(), rank=rank, donor=moved, intersections=hits)
    for w in words:
        counts = [bank.ALL_MAPS] + [0] * (best - 1) if best else []
        for v in reversed(physical(w)[1:]):
            good = allowed[v]
            counts = [(word & good) | (counts[j-1] & ~good if j else 0) for j, word in enumerate(counts)]
            if not any(counts):
                break
        assert not any(counts)
    return best, example


def run(folder, length, label, records, iterations=1700):
    pool = library()
    paths = [list(physical(w)) for w in pool]
    words = segments(pool, 94, max(98, length))
    targets = sorted({w[:length] for w in words if len(w) >= length})
    keys = sorted(words)
    images = list(bank.permutation_images())
    ledger = {}
    for k, r in records.items():
        p = r["parent"]
        allowed = bank.allowed_maps(p, images)
        score, closest = minimum_overlap(targets, allowed, images, p)
        best = bank.longest(keys, allowed)
        placed = bank.make_witness(paths, words[best[1]], best, p)
        start = max([placed["partner"], *r["partners"].values()], key=len)
        ledger[k] = dict(parent=p, published=bool(r["partners"]), minimum=score,
                         closest=closest, placement=placed, best=checked(p,start))
    # Try the best placements at previously unrepresented ends and the least obstructed published ends.
    selected = []
    for known in (False, True):
        subset = [k for k in ledger if ledger[k]["published"] == known]
        selected += sorted(subset, key=lambda k:(ledger[k]["minimum"],-ledger[k]["best"]["edges"],k))[:8]
    with TemporaryDirectory() as tmp:
        exe = Path(tmp) / "Grow.exe"
        source = MS / "265-joint-arm-regrowth/JoinedSearch.cs"
        subprocess.run([str(CSC), "/nologo", "/optimize+", "/out:"+str(exe), str(source)],check=True,capture_output=True)
        for i,k in enumerate(selected):
            row=ledger[k]
            p,b = row["parent"], row["best"]["B"]
            seed=268000+i
            log=subprocess.run([str(exe),str(seed),str(iterations),"fixed"],text=True,capture_output=True,check=True,
                               input="".join(",".join(map(str,q))+"\n" for q in (p,b))).stdout.splitlines()
            a, moved = (list(map(int,line.split(","))) for line in log[:2])
            assert a==p and len(moved)>=len(b)
            row["regrowth"]=dict(seed=seed,iterations=iterations,start_edges=row["best"]["edges"])
            row["best"]=checked(p,moved)
    for r in ledger.values():
        seq = r["best"]["joined"]
        assert len(seq)==len(set(seq)) and all(0<=v<512 for v in seq)
        for i,u in enumerate(seq):
            assert {u^(1<<j) for j in range(9)} & set(seq)==set(seq[max(0,i-1):i]+seq[i+1:i+2])
    result=dict(target_partner_edges=length,target_words=len(targets),permutations=len(images),
                placements=len(records)*len(targets)*len(images),minima=Counter(r["minimum"] for r in ledger.values()),
                longest=max(r["best"]["edges"] for r in ledger.values()),roots=ledger)
    write(folder / label, result)
    print({k:v for k,v in result.items() if k!="roots"}, flush=True)
    return result


if __name__=="__main__":
    roots=read(MS/"266-rebuilding-one-arm/parents.json")["parents"]
    run(HERE,97,"placements.json",{k:r for k,r in roots.items() if r["retain_edges"]==94 and not r["from_191"]})
