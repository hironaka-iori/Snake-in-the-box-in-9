"""Bounded saved-cycle and catalogue review. No solver, Lean, or graph loading."""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
pins = {}

def read(relative):
    raw = (ROOT / relative).read_bytes()
    pins[relative] = {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}
    return json.loads(raw)

def pin_text(relative):
    raw = (ROOT / relative).read_bytes()
    pins[relative] = {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}
    return raw.decode("utf-8-sig")

def canon(word):
    names = {}
    return tuple(names.setdefault(x, len(names)) for x in word)

def shape(word):
    return min(canon(word), canon(word[::-1]))

def decode(code, length=6):
    return [code // 6**i % 6 + 1 for i in range(length-1, -1, -1)]

def vertices(word):
    out = [0]
    for d in word:
        out.append(out[-1] ^ (1 << d))
    return out

results = read("milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json")
credit = read("milestones/132-odd-pair-endpoint/data/credit-limitation.json")
model = read("milestones/59-extended-share-window/extended/data/model.json")
catalogue = read("milestones/39-audited-bound-236/data/exclusion-catalogue.json")
source72 = read("milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json")
cases72 = read("milestones/72-four-count-proof-closure/data/cases.json")
audit72 = read("milestones/72-four-count-proof-closure/data/proof-audit.json")
completed73 = read("milestones/73-countfree-share-catalogue/data/proved-model.json")
src42 = pin_text("milestones/42-six-count-state-model/scripts/model.py")
src59 = pin_text("milestones/59-extended-share-window/scripts/extend.py")
src72 = pin_text("milestones/72-four-count-proof-closure/scripts/graph.py")
src131 = pin_text("milestones/131-odd-pair-six-count/scripts/evaluate_graph.py")
assert "Symbol6 denotes [6,21]" in src42
assert "indices=[offset+(5-j if reverse else j)-3" in src72
assert "five = values[:,s:s+5]" in src131
assert "word[s+2:s+8]" in src131
assert "C=W[-6:-1]" in src59
assert len(catalogue) == 732
assert set(source72["applied_cases"]) <= set(audit72["completed_cases"])

profile = next(p for p in results["profiles"] if p["profile"] == "conditional_floor18")
cycle = profile["cycle"]
first = next(p for p in credit["cycles"] if p["source_profile"] == "conditional_floor18")
assert len(cycle) == 7
assert [e["edge"] for e in cycle] == [e["edge"] for e in first["rows"]]
period = [e["counts"][0] for e in cycle]
assert period == [3,3,5,2,6,6,3]
keys = set()
for ds, cs in catalogue:
    keys.add((canon(ds), tuple(cs)))
    keys.add((canon(ds[::-1]), tuple(cs[::-1])))
selected72 = [c for c in cases72 if c["number"] in source72["applied_cases"]]
groups = defaultdict(list)
rows = []
all_catalogue_hits = []
all_72_hits = []
for i, edge in enumerate(cycle):
    nxt = cycle[(i+1) % 7]
    word, counts = edge["directions"], edge["counts"]
    assert word == model["extensions"][edge["direction"]]
    assert decode(edge["count_code"]) == counts
    assert edge["v"] == nxt["u"]
    assert canon(word[1:]) == canon(nxt["directions"][:-1])
    assert counts[1:] == nxt["counts"][:-1]
    assert counts == [period[(i+j) % 7] for j in range(6)]
    path = vertices(word)
    assert len(set(path)) == 10
    assert all((path[a] ^ path[b]).bit_count() != 1
               for a in range(10) for b in range(a+2, 10))
    exact = []
    for length in range(2, 6):
        for j in range(7-length):
            ds = canon(word[j+2:j+length+3])
            cs = tuple(counts[j:j+length])
            if (ds, cs) in keys:
                all_catalogue_hits.append([i, j, length, list(ds), list(cs)])
            if 6 not in cs:
                item = {"row": i, "edge": edge["edge"], "count_start": j,
                        "direction_start": j+2, "centre_positions": list(range(j+3,j+3+length)),
                        "period_phase": (i+j) % 7}
                groups[(ds, cs)].append(item)
                exact.append({"directions": list(ds), "counts": list(cs), **item})
    for case in selected72:
        for offset in range(2, 5):
            for reverse in [False, True]:
                ds = word[offset:offset+5]
                if canon(ds[::-1] if reverse else ds) != tuple(case["dirs"]):
                    continue
                indices = [offset+(5-j if reverse else j)-3 for j in range(1,5)]
                intervals = [(6,21) if counts[j] == 6 else (counts[j],counts[j]) for j in indices]
                if all(lo <= a and b <= hi for (a,b),(lo,hi) in zip(intervals,case["bounds"])):
                    all_72_hits.append([i,case["number"],offset,reverse])
    pair_matches = [s for s in range(2) if shape(word[s+2:s+8]) == (0,1,2,0,3,2)]
    assert not pair_matches
    assert shape(word[2:]) != shape((0,1,2,3,1,0,4))
    assert edge["shared_bonus"] == 0
    rows.append({"row": i, "edge": edge["edge"], "u": edge["u"], "v": edge["v"],
                 "direction_index": edge["direction"], "directions": word, "vertices": path,
                 "count_code": edge["count_code"], "count_positions": list(range(3,9)),
                 "counts": counts, "intervals": [[6,21] if c == 6 else [c,c] for c in counts],
                 "conditional_weight": edge["weight"],
                 "completed_weight_on_same_edge": first["rows"][i]["first_profile_weight"],
                 "exact_low_subwindows": exact})
assert not all_catalogue_hits and not all_72_hits
assert sum(e["weight"] for e in cycle) == 3472
assert Fraction(3472,7) == 496
assert sum(first["weights"]) == 3453
assert first["mean"] == str(Fraction(3453,7))
motif = groups[((0,1,2,3,0,1),(3,3,3,5,2))]
triple = groups[((0,1,2,3),(3,3,3))]
assert [(x["row"],x["count_start"]) for x in motif] == [(5,1),(6,0)]
assert len(triple) == 4 and {x["period_phase"] for x in triple} == {6}
assert ((0,1,2,0),(3,3,3)) in keys
assert ((0,1,2,3),(3,3,3)) not in keys

window = vertices([0,1,2,3])
common = [x for x in range(512) if (x^window[1]).bit_count()==2 and (x^window[3]).bit_count()==2]
forced = {x^(1<<d) for x in window[1:-1] for d in range(9)}-set(window)
allowed = [x for x in common if x not in forced]
assert allowed == [4,13,21,37,69,133,261]

native = {}
for tag in ["base", "short"]:
    prefix = f"milestones/138-seven-cycle-endpoints/work/{tag}/"
    enc = read(prefix+"encoding.json")
    run = read(prefix+"run-status.json")
    assert run["status"] == "UNSAT_UNCERTIFIED"
    assert not enc["forbidden_endpoints"]
    native[tag] = {"status":run["status"], "directions":enc["directions"],
                   "bounds":enc["bounds"], "forbidden_endpoints":enc["forbidden_endpoints"],
                   "trace_replayed_by_this_audit":False}
assert native["short"]["directions"] == [0,1,2,3,0,1]
assert native["short"]["bounds"] == [[0,3],[0,3],[0,3],[0,5],[0,2]]
closure = [0,1,3,7,15,14,12,8]
assert len(set(closure)) == 8
assert all(((closure[i]^closure[j]).bit_count()==1) ==
           ((j-i)==1 or (i,j)==(0,7)) for i in range(8) for j in range(i+1,8))
assert set(closure)-set(vertices([0,1,2,3,0,1])) == {8}

record = {
    "status":"PASS_BOUNDED_SAVED_CYCLE_AND_CATALOGUE_REVIEW",
    "source_pins":pins,
    "rows":rows,
    "count_alignment":{"vertices":list(range(3,9)),"five_count_placement_s":"directions[s+2:s+8], counts[s:s+5]","six_symbol_interval":[6,21]},
    "count_period":period,
    "profiles":{"conditional_floor18":{"weights":[e["weight"] for e in cycle],"sum":3472,"mean":"496","attaining_for_saved_profile":True},
                "completed_on_same_seven_cycle":{"weights":first["weights"],"sum":3453,"mean":"3453/7","attaining_for_completed_profile":False,"completed_saved_minimum":"488"}},
    "shared_low_motif":{"directions":[0,1,2,3,0,1],"counts":[3,3,3,5,2],"appearances":motif,"events_per_period":1},
    "smaller_shared_triple":{"directions":[0,1,2,3],"counts":[3,3,3],"appearances":triple,"events_per_period":1},
    "exact_subwindow_groups":[{"directions":list(k[0]),"counts":list(k[1]),"appearances":v} for k,v in sorted(groups.items())],
    "catalogue_checks":{"catalogue39_entries":732,"catalogue39_hits":all_catalogue_hits,"completed72_cases":source72["applied_cases"],"completed72_hits":all_72_hits,
        "nearby_existing_exclusions":[{"directions":[0,1,2,0],"counts":[3,3,3]},{"directions":[0,1,2,3,0,1],"counts":[3,3,3,3,3]},{"directions":[0,1,2,3,0,1],"counts":[3,3,3,3,4]}],
        "countfree73_is_not_an_exclusion_catalogue":True,"all_catalogues_or_prior_art_exhaustively_searched":False},
    "native_followup":native,
    "eight_cycle_geometry":{"cyclic_order":closure,"additional_vertex":8,"induced_cycle_checked":True,"count_caps_force_additional_vertex_proved_here":False},
    "selected_current_route":"Certify the ordinary 012301 upper-cap exclusion (3,3,3,5,2); no endpoint premise is used by the recorded short query.",
    "one_future_endpoint_candidate":{"status":"UNPROVED_FUTURE_ONLY","hypotheses":"Actual induced path in Q9, fitting canonical0123 window, exact three internal counts3,3,3.","conclusion":"One actual endpoint is at Hamming distance2 from both outer internal centres.","normalized_window":window,"common_sphere":common,"degree_compatible_endpoint_positions":allowed,"reason_for_small_first_test":"Only four directions, three exact count restrictions, and seven forbidden-endpoint units; appears once per saved period."},
    "limitations":["No solver, Lean, or full graph evaluation was run.","No original NPZ arrays were loaded; row indices and weights are retained saved evidence, while metadata directions, count-code decoding, overlaps and catalogue matches were independently reconstructed.","Native138 run statuses are pinned observations; their proof traces were not checked here.","No arbitrary-snake cycle realization, universal endpoint theorem, novelty assertion, or global upper bound is established."]
}
record["checker_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
destination = HERE/"data/cycle-review.json"
destination.write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"status":record["status"],"rows":len(rows),"catalogue_hits":len(all_catalogue_hits)+len(all_72_hits),"short_motif_appearances":len(motif),"short_motif_events":1,"record_sha256":hashlib.sha256(destination.read_bytes()).hexdigest()},indent=2))
