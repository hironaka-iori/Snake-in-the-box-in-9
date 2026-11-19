"""Compare Q8 representatives, all endpoint extensions, and Q9 one-crossing arms."""
from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "243-coil-opening"))
from open_coil import verify
from census191 import signature

N = [{v ^ (1 << j) for j in range(8)} for v in range(256)]


def extensions(path):
    chosen = set(path)
    for left in (True, False):
        end = path[0] if left else path[-1]
        for z in sorted(N[end] - chosen):
            if N[z] & chosen == {end}:
                yield ([z] + path if left else path + [z])


def describe(path):
    verify(path, False)
    if max(path) >= 256:
        raise ValueError("Outside the eight-cube")
    chosen = set(path)
    steps = [(a ^ b).bit_length()-1 for a,b in zip(path,path[1:])]
    first = list(extensions(path))
    second = {tuple(new) for p in first for new in extensions(p)}
    capacities = [sum(N[z] & chosen == {end} for z in N[end] - chosen) for end in (path[0],path[-1])]
    flips = []
    for i in range(1,len(path)-1):
        z = path[i-1] ^ path[i] ^ path[i+1]
        if z not in chosen and (N[z] & chosen) == {path[i-1],path[i+1]}:
            flips.append(i)
    return dict(length=len(path)-1,endpoint_distance=(path[0]^path[-1]).bit_count(),
                crossings=sorted(Counter(steps).values()),endpoint_additions=capacities,
                two_step_paths=len(second),two_step_classes=len({signature(p) for p in second}),
                square_flip_indices=flips,
                outside_neighbour_histogram=dict(sorted(Counter(len(N[z]&chosen) for z in range(256) if z not in chosen).items())))


def split(path, axis, index):
    low=(1 << axis)-1
    def project(v):
        return (v & low) | ((v >> (axis+1)) << axis)
    root = project(path[index])
    first=[project(v)^root for v in reversed(path[:index+1])]
    second=[project(v)^root for v in path[index+1:]]
    return sorted((first,second),key=len,reverse=True)


def main():
    q8 = ROOT / "outputs/snake8_witness.json"
    bank = ROOT / "work/bank9.json"
    reference = ROOT / "outputs/joint_layer_seed.json"
    p = json.loads(q8.read_bytes())["vertex_sequence"]
    joined = json.loads(reference.read_bytes())
    groups = {}
    pairs = []
    for seed, record in enumerate(json.loads(bank.read_bytes())):
        path=record["vertex_sequence"]
        axes=defaultdict(list)
        for i,(a,b) in enumerate(zip(path,path[1:])):
            axes[(a^b).bit_length()-1].append(i)
        for axis,locations in axes.items():
            if len(locations)!=1:
                continue
            a,b=split(path,axis,locations[0])
            if (len(a),len(b))!=(97,95) or set(a)&set(b)!={0}:
                raise ValueError("Unexpected arm sizes or contact")
            verify(a,False)
            verify(b,False)
            verify(a[::-1]+[256+v for v in b],False)
            pairs.append(dict(seed=seed,axis=axis,long=a,short=b))
            for arm in (a,b):
                key=(len(arm),signature(arm))
                if key not in groups:
                    groups[key]=dict(first_seed=seed,path=arm,frequency=0,properties=describe(arm))
                groups[key]["frequency"]+=1
    paths={"optimal_98":p, "first_97_vertices":p[:97], "middle_97_vertices":p[1:-1],
           "last_97_vertices":p[-97:], "published_96_arm":joined["left_path"],
           "published_94_partner":joined["right_path"]}
    examples={key:dict(path=path,properties=describe(path)) for key,path in paths.items()}
    data=dict(inputs={f.name:sha256(f.read_bytes()).hexdigest() for f in (q8,bank,reference)},
              examples=examples,arm_classes=list(groups.values()),one_crossing_pairs=pairs)
    (HERE/"comparison.json").write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    for key,r in examples.items():
        d=r["properties"]
        print(key,d["endpoint_distance"],d["crossings"],d["endpoint_additions"],d["two_step_paths"],len(d["square_flip_indices"]))
    print("bank pairs",len(pairs),"arm classes",[(g["properties"]["length"],g["frequency"]) for g in groups.values()])


if __name__=="__main__":
    main()
