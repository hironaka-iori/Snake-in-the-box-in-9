"""Test joint chronological triples after full round-215 propagation on its five regions."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from solve import save

COMMIT = "670d633bca81e3efff8d8ba5db0a1ba7079af137"
MILESTONE = "milestones/215-word-partner-capacity/"
STATE = "1e53d7824e4350092104072ba5c1506236f8af19969f09346ab3c3f517e7eacb"
FULL = (1<<64)-1


def get(path):
    return subprocess.check_output(["git","show",COMMIT+":"+MILESTONE+path])


def values(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask -= bit


def audit_triples(domains, rows):
    removed_pairs = []
    removed_values = set()
    counts = {"longer_than_two":0,"empty_middle_at_zero":0,"empty_middle_at_two":0}
    triples = []
    for i in range(len(domains)-2):
        j,k = i+1,i+2
        supported = [0,0,0]
        step = {}
        outer = rows.get((i,k),[FULL]*64)
        for a in values(domains[i]):
            for c in values(domains[k] & outer[a]):
                # Binary closure may leave (a,c) without any common middle.
                forward = domains[j] & rows[i,j][a]
                middle = sum(1<<b for b in values(forward) if rows[j,k][b]>>c&1)
                direct = sum(1<<b for b in values(domains[j]) if
                             (a^b).bit_count()==1 and (b^c).bit_count()==1 and
                             rows[i,j][a]>>b&1 and rows[j,k][b]>>c&1)
                assert middle == direct
                if not middle:
                    removed_pairs.append([i,a,c])
                    h=(a^c).bit_count()
                    assert h in (0,2,4,6)
                    counts["longer_than_two" if h>2 else
                           ("empty_middle_at_two" if h else "empty_middle_at_zero")]+=1
                else:
                    for b in values(middle):
                        step.setdefault((a,b),set()).add((b,c))
                    supported[0] |= 1<<a
                    supported[1] |= middle
                    supported[2] |= 1<<c
        for x,mask in zip((i,j,k),supported):
            removed_values.update((x,v) for v in values(domains[x]&~mask))
        triples.append(step)
    # Enforce every neighbouring triple simultaneously, retaining an adjacent
    # ordered pair as the boundary value shared by neighbouring triples.
    layers=[set(triples[0])]
    for step in triples:
        layers.append({right for left in layers[-1] for right in step.get(left,())})
    for i in reversed(range(len(triples))):
        layers[i]={left for left in layers[i] if triples[i].get(left,set()) & layers[i+1]}
    kept=[set() for _ in domains]
    for i,layer in enumerate(layers):
        for a,b in layer:
            kept[i].add(a)
            kept[i+1].add(b)
    chain=sorted((i,a) for i,mask in enumerate(domains) for a in values(mask) if a not in kept[i])
    return removed_pairs, sorted(removed_values), counts, chain


def check_pair_closure(domains,rows,executable):
    n=len(domains)
    data=[str(n)," ".join(map(str,domains))]
    for i in range(n):
        for j in range(i+1,n):
            data.append(" ".join(map(str,rows.get((i,j),[FULL]*64))))
    proc=subprocess.run([str(executable)],input="\n".join(data),capture_output=True,
                        text=True,check=True)
    header,*rest=proc.stdout.splitlines()
    sweeps,deleted,i,j=map(int,header.split())
    record=dict(sweeps=sweeps,removed_pairs=deleted)
    if i>=0:
        record["empty_pair"]=[i,j]
        return record
    closed=list(map(int,rest[0].split()))
    assert len(closed)==n and all(x&~y==0 for x,y in zip(closed,domains))
    record["deleted_values"]=[(i,v) for i,(d,c) in enumerate(zip(domains,closed)) for v in values(d&~c)]
    return record


def scan(compiler,pairs,probe_all):
    state_raw = get("data/case-22/state.json")
    assert sha256(state_raw).hexdigest() == STATE
    state = json.loads(state_raw)
    files = {name:get("data/case-22/"+name) for name in ("model.json","permutations.json","input-tail.txt")}
    for name,raw in files.items():
        assert sha256(raw).hexdigest() == state["model_pins"][name]
    model = json.loads(files["model.json"])
    perms = json.loads(files["permutations.json"])
    engine = get("scripts/word_solver.c")
    assert sha256(engine).hexdigest() == state["engine_pins"]["scripts\\word_solver.c"]
    marker = b"  started=GetTickCount64();int result=visit(initial);"
    assert engine.count(marker) == 1
    # Leave all propagation rules and the input parser byte-identical.
    # Replace traversal/output with a single call and a dump of the root domains.
    observe = b'  int ok=propagate(initial); printf("%d",ok); for(int x=0;x<n;x++)printf(" %llu",initial[x]); puts("");\n'
    if probe_all:
        observe += b'''
  if(ok) for(int i=0;i<n;i++) {
    uint64_t allowed=initial[i];
    if(!(allowed&(allowed-1)))continue;
    while(allowed) {
      int w=__builtin_ctzll(allowed); allowed&=allowed-1;
      uint64_t fixed[NMAX];
      memcpy(fixed,initial,n*sizeof(uint64_t)); fixed[i]=BIT(w);
      if(!propagate(fixed)) printf("%d %d\\n",i,w);
    }
  }
'''
    observe+=b' return 0;\n}\n'
    observe_source = engine.split(marker)[0]+observe
    result = dict(commit=COMMIT,state_sha256=STATE,observed_source_sha256=sha256(observe_source).hexdigest(),regions=[])
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        src = work/"observe.c"
        src.write_bytes(observe_source)
        exe = work/"observe.exe"
        subprocess.run([str(compiler),"-O2",str(src),"-o",str(exe)],check=True)
        n = model["variables"]
        for job in state["frontier"]:
            ds = job["domains"]
            head = (f'{n} 64 {len(model["constraints"])} {len(model["nogoods"])} {len(perms)}\n60 1\n'
                    +" ".join(map(str,ds))+"\n").encode("ascii")
            proc = subprocess.run([str(exe)],input=head+files["input-tail.txt"],
                                  capture_output=True,check=True)
            first,*probes=proc.stdout.splitlines()
            ok,*closed = map(int,first.split())
            assert len(closed) == n and all(x&~y==0 for x,y in zip(closed,ds))
            row = dict(region=job["id"],baseline_consistent=bool(ok))
            if probe_all:
                row["singleton_rejections"]=[list(map(int,line.split())) for line in probes]
            if ok:
                rows = {(c["x"],c["y"]):c["rows"] for c in model["constraints"]}
                assert len(rows)==len(model["constraints"])
                invalid, deletes, counts, chain = audit_triples(closed,rows)
                row.update(unsupported_pair_count=len(invalid),examples=invalid[:4],
                           pair_counts=counts,unsupported_values=deletes,chain_value_removals=chain,
                           baseline_values=sum(m.bit_count() for m in closed))
                if pairs is not None:
                    row["arbitrary_triples"]=check_pair_closure(closed,rows,pairs)
                    for x,w in row["arbitrary_triples"].get("deleted_values",[]):
                        fixed=closed.copy()
                        assert fixed[x]>>w&1
                        fixed[x]=1<<w
                        fixed_head=(head.splitlines(keepends=True)[:2])
                        fixed_input=b"".join(fixed_head)+(" ".join(map(str,fixed))+"\n").encode("ascii")
                        check=subprocess.run([str(exe)],input=fixed_input+files["input-tail.txt"],
                                             capture_output=True,check=True)
                        survives=int(check.stdout.split()[0])
                        row.setdefault("fixed_word_baseline",[]).append([x,w,survives])
            if probe_all:
                print("singleton contradictions",len(probes),flush=True)
            print(row["region"],bool(ok),row.get("pair_counts"),len(row.get("unsupported_values",[])),
                  len(row.get("chain_value_removals",[])),flush=True)
            result["regions"].append(row)
    save(Path("parent-triples-215.json"),result)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--cc",type=Path,required=True)
    parser.add_argument("--pairs",type=Path)
    parser.add_argument("--probe-all",action="store_true")
    args=parser.parse_args()
    scan(args.cc.resolve(),args.pairs.resolve() if args.pairs else None,args.probe_all)
