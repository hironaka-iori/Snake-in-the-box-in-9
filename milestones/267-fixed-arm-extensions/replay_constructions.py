"""Independently check the opposite-arm graph, its placements and the bounded fixed-parent walks."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import gzip
import importlib.util
import json
import subprocess

from donors import HERE, MS, seeds,read,write,bank
from prepare import LAST

path265=MS/"265-joint-arm-regrowth/audit.py"
spec=importlib.util.spec_from_file_location("independent_geometry",path265)
geom=importlib.util.module_from_spec(spec)
spec.loader.exec_module(geom)

def vertices(word):
    a=[0]
    for d in word:
        a.append(a[-1]^(1<<d))
    return tuple(a)

def directed(p):
    return geom.pattern([u^v for u,v in zip(p,p[1:])])

def check_donors():
    data=read(HERE/"donors.json")
    raw=(HERE/"donor-paths.json.gz").read_bytes()
    assert sha256(raw).hexdigest()==data["sha256"] and data["closed"]
    rows=json.loads(gzip.decompress(raw))
    words=[bytes.fromhex(w) for w,_ in rows]
    assert len(set(words))==len(words)==data["expanded"]
    start,hashes=seeds()
    assert data["sources"]==hashes and words[:len(start)]==start
    required=[set() for w in words]
    for i,(w,parent) in enumerate(rows):
        if i>=len(start):
            assert 0<=parent<i
            required[parent].add(bytes.fromhex(w))
    allowed=set(words)
    links=0
    candidate_words={95:set(),96:set()}
    for i,w in enumerate(words):
        original=vertices(w)
        geom.verify(list(original))
        neighbours=set()
        for seq in (original,original[::-1]):
            arm=tuple(v^seq[0] for v in seq)
            for p,_ in geom.edits(arm):
                if len(p)>=96:neighbours.add(geom.path_class(p))
            for n,patterns in candidate_words.items():
                for j in range(len(arm)-n):
                    patterns.add(directed(arm[j:j+n+1]))
        assert required[i]<=neighbours<=allowed
        links+=len(neighbours)
    return candidate_words,links


def check_placements(patterns):
    data=read(HERE/"cases.json")
    table=read(HERE/"placements.json")["roots"]
    images=list(bank.permutation_images())
    points={n:[vertices(w)[1:] for w in sorted(ws)] for n,ws in patterns.items()}
    checked=Counter()
    for k,r in data["roots"].items():
        p=r["parent"]
        n=192-len(p)
        row=table[k]["expanded_placement"]
        assert p==row["parent"] and geom.verify(row["joined"])==row["joined_edges"]
        flags=bank.allowed_maps(p,images)
        for sequence in points[n]:
            live=bank.ALL_MAPS
            for v in reversed(sequence):
                live &= flags[v]
                if not live:break
            assert not live,(k,n)
        checked[n]+=len(points[n])
    return dict(rooted_targets={n:len(v) for n,v in points.items()},root_word_pairs=checked,permutations=len(images))


def check_walks(executable):
    data=read(HERE/"cases.json")["roots"]
    out={}
    for file in sorted(HERE.glob("single-*.json")):
        log=read(file)
        count=0
        for k,r in log["roots"].items():
            parent=data[k]["parent"]
            blocks=frozenset(parent[1:])
            assert geom.verify(r["best_path"])==len(r["best_path"])-1
            route=r["best_arm_route"]
            assert route[0] in data[k]["partners"].values()
            for old,new in zip(route,route[1:]):
                assert any(q==tuple(new) and not s&blocks for q,s in geom.edits(tuple(old)))
            if not r["closed"]:continue
            inputs=[parent,*data[k]["partners"].values()]
            answer=subprocess.run([str(executable),str(log["minimum"])],text=True,capture_output=True,check=True,
                       input="".join(",".join(map(str,p))+"\n" for p in inputs)).stdout.split()
            states,moves,digest=answer
            assert (int(states),int(moves),digest)==(r["visited"],r["moves"],r["states_sha256"]),(k,answer,r["visited"])
            count+=int(states)
        out[file.name]=dict(complete=sum(r["closed"] for r in log["roots"].values()),replayed_states=count,
                            total_visited=sum(r["visited"] for r in log["roots"].values()),
                            best=max(len(r["best_path"])-1 for r in log["roots"].values()))
    return out


if __name__=="__main__":
    patterns,links=check_donors()
    from growth import CSC
    with TemporaryDirectory() as d:
        exe=Path(d)/"ReplayArm.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(HERE/"ReplayArm.cs")],check=True,capture_output=True)
        result=dict(donor_links=links,placement_audit=check_placements(patterns),walks=check_walks(exe),
                    graph_replay_source_sha256=sha256((HERE/"ReplayArm.cs").read_bytes()).hexdigest())
    write(HERE/"construction-audit.json",result)
    print(result)
