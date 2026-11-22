"""Build the exchange graph, recover its three smaller components and verify a longest join."""
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0,str(MS/"255-parity-exchange-arms"))
from enumerate_arms import word
from geometry import extensions
sys.path.insert(0,str(MS/"251-eighty-edge-segments"))
from bank_capacity import check_path

def digest(p): return sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_bytes())

def connected(start, graph):
    reached={start}
    queue=[start]
    for v in queue:
        for w in sorted(graph[v]-reached):
            reached.add(w)
            queue.append(w)
    return reached

base=MS/"255-parity-exchange-arms/attainer-closure.json"
prior=load(base)
old=set(prior["paths"])
paths=dict(prior["paths"])
small={k:set(r["outgoing"]) for k,r in prior["expanded"].items()}
all_moves=defaultdict(set)
pins={base}
r258=MS/"258-four-exchange-parents"
for f in sorted(r258.glob("shell-*.json")):
    four=load(f)
    k=four["reference_shape"]
    for folder in ("256-two-exchange-parents","257-three-exchange-parents"):
        prev=MS/folder/f.name
        pins.add(prev)
        row=load(prev)
        if row["reference_shape"]!=k: raise ValueError("Reference has changed")
        small[k].update(row["shapes"])
    all_moves[k]=small[k]|set(four["shapes"])
    pins.add(f)
for f in sorted(HERE.glob("shell-*-0.json")):
    p=load(f)["reference"]
    k=sha256(word(p)).hexdigest()
    paths[k]=p
    small[k]=set()
    for distance in range(5):
        source=HERE/("shell-"+k[:12]+"-"+str(distance)+".json")
        row=load(source)
        if row["reference"]!=p or row["radius"]!=distance: raise ValueError("Missing shell")
        if distance:
            receipt=HERE/("coverage-"+source.name)
            replay=load(receipt)
            if (digest(source),row["survivor_digest"],row["supply_survivors"])!=(
                    replay["shell_sha256"],replay["ordered_survivor_sha256"],replay["physical_survivors"]):
                raise ValueError("Supply replay differs")
            pins.add(receipt)
        pins.add(source)
        all_moves[k].update(row["shapes"])
        if distance<4: small[k].update(row["shapes"])
if set(connected(min(old),all_moves))!=set(paths) or set(all_moves)!=set(paths):
    raise ValueError("The search frontier is open or disconnected")
for graph in (all_moves,small):
    if any(k not in graph[m] for k,neighbours in graph.items() for m in neighbours):
        raise ValueError("Moves must be reversible up to isometry")
parts = {tuple(sorted(connected(k,small))) for k in paths}
groups = sorted(parts,key=len,reverse=True)
if [len(g) for g in groups]!=[6,4,2] or set(groups[0])!=old: raise ValueError("Group sizes differ")
level={k:i for i,g in enumerate(groups) for k in g}
bridges=sorted((k,m) for k in paths for m in all_moves[k] if level[k]<level[m])
if [(level[k],level[m]) for k,m in sorted(bridges,key=lambda pair:level[pair[0]])]!=[(0,1),(1,2)]:
    raise ValueError("Quotient is not a path with unique bridges")
prior_bank=set().union(*(load(MS/f)[field] for f,field in [
    ("253-repeated-segment-growth/closure.json","paths"),("254-distant-arm-partners/parity-families.json","shapes"),
    ("255-parity-exchange-arms/focus-closure.json","paths")]))
if len(prior_bank)!=264 or (set(paths)-old)&prior_bank: raise ValueError("Earlier inventory differs")
for k,p in paths.items():
    if sha256(word(p)).hexdigest()!=k or len(p)!=97 or check_path(p,8)!=4656 or list(extensions(tuple(p))):
        raise ValueError("Parent shape or extension status differs")
roots=set()
for folder in (HERE,r258):
    receipt=folder/"partner-replay-95.json"
    replay=load(receipt)
    if replay["ledger_sha256"]!=digest(folder/"partner-caps.json"): raise ValueError("Stale certificate")
    for r in replay["roots"]:
        if r["status"]!="excluded" or r["partner_edges"]!=95: raise ValueError("Open partner root")
        roots.add((r["shape"],r["end"]))
    pins.add(receipt)
if roots!={(k,e) for k in set(paths)-old for e in (0,1)}: raise ValueError("Incomplete partner coverage")
attaining=MS/"248-rooted-arm-capacity/attainers.json"
parent_source=MS/"248-rooted-arm-capacity/endpoint94.json"
parent=next(r["rooted_parent"] for r in load(parent_source)["records"] if r["case"]==[0,0])
partner=next(r["paths"][0]["path"] for r in load(attaining)["records"] if r["class_id"]==0)
join=parent[::-1]+[v+256 for v in partner]
if sha256(word(parent)).hexdigest() not in paths or check_path(join,9)!=18336 or len(join)!=192:
    raise ValueError("Attaining join does not have 191 edges")
(HERE/"attaining-191.json").write_text(json.dumps(dict(parent=parent,partner=partner,vertices=join,
    edges=191,distinct_vertices=192,checked_pairs=18336),indent=2)+"\n",encoding="utf-8",newline="\n")
old_upper=MS/"256-two-exchange-parents/summary.json"
if load(old_upper)["maximum_join_in_component"]!=191 or {
        (k,r["end"]) for k,records in prior["rooted_status_through_254"].items() for r in records
        if r["target_192"]=="excluded"}!={(k,e) for k in old for e in (0,1)}:
    raise ValueError("Earlier six-shape result differs")
pins.update([old_upper,attaining,parent_source,HERE/"Bridges259-compile.json",r258/"summary.json",Path(__file__)])
result=dict(round=259,shapes=len(paths),smaller_components=groups,four_exchange_bridges=bridges,
    max_three_neighbours={k:sorted(v) for k,v in small.items()},max_four_neighbours={k:sorted(v) for k,v in all_moves.items()},
    new_endpoint_checks=sorted(roots),extendible_shapes=[],maximum_single_crossing_edges=191,
    maximum_overlap_with_each_of_twelve=43,global_bounds=[191,230],global_independent_upper_rebuild=False,
    inputs={p.relative_to(MS).as_posix():digest(p) for p in sorted(pins)})
(HERE/"component.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
print("components",list(map(len,groups)),"bridges",[(k[:12],m[:12]) for k,m in bridges],"maximum",len(join)-1)
