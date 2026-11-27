"""Identify fixed middle paths at every twice-used coordinate of the two archives."""
from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path
import json, sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent if HERE.parent.name == "milestones" else Path("E:/Snake-in-a-box/milestones")
sys.path.insert(0, str(next(MS.glob("265-*"))))
from exchange import input_paths
from conditional import code

def read(file):
    return json.loads((HERE / file).read_bytes())

def write(file, value):
    (HERE / file).write_bytes((json.dumps(value, separators=(",", ":"))+"\n").encode())

def lift(axis, origin, v):
    bit = 1 << axis
    return origin ^ (v & (bit-1)) ^ ((v & ~(bit-1) & 255) << 1) ^ (bit if v & 256 else 0)

def charts(sequence):
    flips = [a ^ b for a,b in zip(sequence, sequence[1:])]
    for axis in range(9):
        bit = 1 << axis
        cuts = [i for i,k in enumerate(flips) if k == bit]
        if len(cuts) != 2:
            continue
        a,b = cuts
        def project(v):
            return (v & (bit-1)) | ((v >> (axis+1)) << axis)
        parts = [sequence[:a+1][::-1], sequence[a+1:b+1], sequence[b+1:]]
        left, mid, right = [[project(v ^ sequence[a]) for v in p] for p in parts]
        joined = left[::-1]+[256+v for v in mid]+right
        assert sequence == [lift(axis, sequence[a], v) for v in joined]
        yield axis,sequence[a],left,mid,right

def signature(a,m,b):
    # The crossing coordinate is distinguished. Translate the first middle port to zero.
    def directed(left, mid, right):
        order = {}
        def directions(p):
            return bytes(order.setdefault(x^y,len(order)) for x,y in zip(p,p[1:]))
        return directions(mid) + b"\xff" + directions(left) + b"\xff" + directions(right)
    return min(directed(a,m,b), directed(b,m[::-1],a))

def cases(width, minimum=190, full=False):
    if full:
        groups={}; archive={}; counts=Counter()
        for name,path in input_paths():
            archive[code(path)]=name
            if len(path)-1<minimum: continue
            core=path[width:len(path)-width]
            assert len(core)>=3
            k=code(core);counts[len(path)-1]+=1
            row=groups.setdefault(k,dict(a=core[:1],m=core[1:-1],b=core[-1:],source=name,axis=-1,origin=0,occurrences=0,donor_max=0))
            row["occurrences"]+=1;row["donor_max"]=max(row["donor_max"],len(path)-1)
        return groups,archive,dict(chart_occurrences=dict(counts),distinct_retained=len(groups),archive_shapes=len(archive),cube=9)

    unique = {}
    lengths = Counter()
    mids = Counter()
    charts_by_archive = Counter()
    archive = {}
    for name,path in input_paths():
        archive[code(path)] = name
        if len(path)-1 < minimum:
            continue
        for axis,origin,a,m,b in charts(path):
            lengths[len(path)-1] += 1
            mids[len(m)-1] += 1
            charts_by_archive[name] += 1
            l = a[:max(1,len(a)-width)]
            r = b[:max(1,len(b)-width)]
            key = signature(l,m,r)
            if key not in unique:
                unique[key] = dict(a=l, m=m, b=r, source=name, axis=axis, origin=origin,
                                   donor=path, occurrences=0, donor_max=0)
            row = unique[key]
            row["occurrences"] += 1
            row["donor_max"] = max(row["donor_max"],len(path)-1)
    info = dict(chart_occurrences=dict(lengths),sources=dict(Counter(k.split("-")[0] for k in charts_by_archive)),
                middle_lengths=dict(sorted(mids.items())),distinct_retained=len(unique),archive_shapes=len(archive))
    return unique,archive,info

if __name__ == "__main__":
    groups,bank,report = cases(int(sys.argv[1]))
    print(report)

