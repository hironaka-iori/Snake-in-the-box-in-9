"""Reconcile the shell, shape and rooted certificate results."""
from hashlib import sha256
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0,str(MS/"251-eighty-edge-segments"))
from bank_capacity import check_path
sys.path.insert(0,str(MS/"255-parity-exchange-arms"))
from geometry import extensions
from enumerate_arms import word

def load(p): return json.loads(p.read_bytes())
def digest(p): return sha256(p.read_bytes()).hexdigest()

old = load(MS/"255-parity-exchange-arms/attainer-closure.json")["paths"]
arms = load(HERE/"new-arms.json")["shapes"]
caps = load(HERE/"partner-replay-95.json")
if caps["ledger_sha256"] != digest(HERE/"partner-caps.json") or caps["counts"] != {"excluded":2}:
    raise ValueError("Missing unrestricted partner exclusions")
rows = {}
for p in sorted(HERE.glob("shell-*.json")):
    s = load(p)
    r = load(HERE/("coverage-"+p.name))
    if (r["shell_sha256"],r["ordered_survivor_sha256"],r["physical_survivors"]) != (
            digest(p),s["survivor_digest"],s["supply_survivors"]): raise ValueError("Replay mismatch")
    if set(s["shapes"])-set(old)-set(arms): raise ValueError("Additional successor")
    rows[s["reference_shape"]] = dict(label=s["label"], candidates=s["candidate_sets"],
        physical=s["supply_survivors"], supporting=len(s["positive_classes"]), paths=s["labelled_arms"],
        successors=sorted(s["shapes"]), replay_sha256=digest(HERE/("coverage-"+p.name)))
if set(rows)!=set(old) or len(arms)!=1: raise ValueError("Unexpected domain")
for k,p in (old|arms).items():
    if sha256(word(p)).hexdigest()!=k or len(p)!=97 or list(extensions(tuple(p))):
        raise ValueError("Endpoint or shape mismatch")
construct = load(HERE/"constructed.json")
joins = {}
for root,r in construct["cases"].items():
    p = r["parent"][::-1]+[256+v for v in r["partner"]]
    if p!=r["joined"] or check_path(p,9)!=r["verified_pairs"]: raise ValueError("Invalid join")
    joins[root]=len(p)-1
global_witness = load(MS.parent/"outputs/snake9_witness.json")["vertex_sequence"]
if check_path(global_witness,9)!=18336: raise ValueError("191-edge witness differs")
data = dict(round=258, references=rows, total_candidate_pairs=sum(r["candidates"] for r in rows.values()),
            physical_survivors=sum(r["physical"] for r in rows.values()), new_shape=list(arms)[0],
            proper_extensions_for_each_of_the_seven=0, new_roots=caps["roots"], constructed_joins=joins,
            maximum_overlap_with_each_original_reference=43, global_bounds=[191,230],global_witness_pairs=18336)
(HERE/"summary.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8",newline="\n")
