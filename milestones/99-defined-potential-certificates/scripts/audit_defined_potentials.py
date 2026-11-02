"""Independent exact-integer check on every key accepted by retainedDiagram.

Reads executable Lean table literals and saved potentials; imports no builder,
solver, compiler or other research script. Writes only its own JSON receipt.
"""
from pathlib import Path
from collections import Counter
import ast
import gzip
import hashlib
import json
import re
import sys
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "work/solver_packages"))
import numpy as np

def sha(b):
    return hashlib.sha256(b).hexdigest()

PINS = {}
def raw(rel):
    data = (ROOT / rel).read_bytes()
    digest = sha(data)
    assert rel not in PINS or PINS[rel] == digest, ("input changed", rel)
    PINS[rel] = digest
    return data

def text(rel):
    return raw(rel).decode("utf-8-sig")

def read(rel):
    return json.loads(raw(rel))

def literal(source, name):
    m = re.search(r"\bdef " + re.escape(name) + r"\b[^=]*:=\s*", source)
    assert m, name
    at = m.end()
    if source[at] == "#":
        at += 1
    assert source[at] == "[", (name, source[at:at+20])
    depth = 0
    for end in range(at, len(source)):
        depth += (source[end] == "[") - (source[end] == "]")
        if depth == 0:
            return ast.literal_eval(source[at:end+1].replace("#[", "["))
    raise AssertionError(("unterminated literal", name))

def canon(word):
    names = {}
    return tuple(names.setdefault(x, len(names)) for x in word)

def enc(symbols):
    out = 0
    for symbol in symbols:
        out = 6*out + symbol-1
    return out

def main():
    start = time.monotonic()
    diagram_source = text("milestones/88-retention-diagram-certificate/lean/GraphData.lean")
    nodes = literal(diagram_source, "retainedDiagram")
    roots = literal(text("milestones/92-full-witness-batch/lean/BatchContextData.lean"), "recordedClassRoots")
    blocks = literal(text("milestones/92-full-witness-batch/lean/ContextAssignmentData.lean"), "savedBlockClasses")
    dag = json.loads(gzip.decompress(raw("milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz")))
    assert nodes == dag["nodes"] and roots == dag["roots"] and blocks == list(map(tuple, dag["blocks"]))
    assert len(nodes) == 3981 and len(roots) == 127 and len(blocks) == 791
    assert blocks == sorted(blocks) and len(dict(blocks)) == len(blocks)
    assert all(0 <= block < 505*75 and 0 <= cls < 127 for block, cls in blocks)
    assert all(len(row) == 7 and all(0 <= child < len(nodes)+2 for child in row[1:]) for row in nodes)
    for rel in ["milestones/88-retention-diagram-certificate/lean/CoverTree.lean",
                "milestones/88-retention-diagram-certificate/lean/DigitReconstruction.lean",
                "milestones/92-full-witness-batch/lean/DefinedProofGraph.lean",
                "milestones/98-concrete-weight-integration/lean/CombinedWeights98.lean",
                "milestones/95-history-credit-integration/lean/HistoryCreditEvaluator95.lean",
                "milestones/78-numeric-history-transition/lean/StateWalk.lean",
                "milestones/78-numeric-history-transition/lean/NumericTransition.lean",
                "milestones/93-defined-graph-potential/scripts/extract_range_certificates.py"]:
        raw(rel)
    tables = text("milestones/77-direction-state-coverage/lean/DirectionTables.lean")
    extensions, shapes = literal(tables, "extensions"), literal(tables, "shapes")
    prefixes = literal(text("milestones/75-exact-history-bridge/history/lean/ExactHistory.lean"), "prefixes")
    geometry = literal(text("milestones/97-geometric-credit-integration/lean/GeometricData97.lean"), "geometricCredits")
    model = read("milestones/59-extended-share-window/extended/data/model.json")
    old_history = read("milestones/67-critical-family-charge/data/full-model.json")
    assert extensions == model["extensions"] and shapes == model["direction_shapes"]
    assert prefixes == old_history["prefixes"] and len(geometry) == len(extensions) == 505
    assert geometry == [p["share_lower"] for p in read("milestones/59-extended-share-window/data/geometry.json")["patterns"]]
    signatures = {}
    history_rules = {}
    for batch in range(11):
        sig_source = text(f"milestones/94-history-share-dispatch/lean/ShareCover{batch:02d}.lean")
        for name in re.findall(r"def (signature\d+)\b", sig_source):
            signatures[name] = literal(sig_source, name)
        rule_source = text(f"milestones/95-history-credit-integration/lean/ConcreteRules95Batch{batch:02d}.lean")
        for name, sig, variant, caps, geo, strong in re.findall(
            r"def (rule\d+) : Rule :=\s*⟨(signature\d+), (variants\d+), (\[[^\n]*\]), (\d+), (\d+)⟩", rule_source):
            history_rules[name] = (signatures[sig], ast.literal_eval(caps), int(geo), int(strong))
    concrete_source = text("milestones/95-history-credit-integration/lean/ConcreteRules95.lean")
    ordered_names = re.search(r"def concreteRules : List Rule :=\s*\[([^]]*)\]", concrete_source).group(1)
    ordered_names = [x.strip() for x in ordered_names.split(",")]
    assert len(ordered_names) == 55 and set(ordered_names) == set(history_rules)
    histories = [history_rules[name] for name in ordered_names]
    old_shares = [p for p in old_history["patterns"] if p["mode"] == "share"]
    assert histories == [(p["signature"], [(int(k),v) for k,v in p["caps"].items()], p["geometric_lower"], p["lower"]) for p in old_shares]
    cond_source = text("milestones/98-concrete-weight-integration/lean/CountConditionedCredits98.lean")
    cond_body = cond_source.split("def conditionedCredit", 1)[1].split("theorem", 1)[0]
    rules = [(tuple(ast.literal_eval(w)), tuple(ast.literal_eval(s)), int(k)+1)
             for w,s,k in re.findall(r"ruleCredit (\[[^]]+\]) (\[[^]]+\]) (\d+) di code", cond_body)]
    assert len(rules) == 5 and [r[2] for r in rules] == [48,96,96,96,120]
    floor_source = text("milestones/98-concrete-weight-integration/lean/CountFreeCredits98.lean")
    floors = {}
    for name in ["completed", "conditional"]:
        body = floor_source.split(f"def {name}Floor", 1)[1].split("def ", 1)[0]
        floors[name] = {tuple(ast.literal_eval(w)):int(v) for w,v in re.findall(r"if cs = (\[[^]]+\]) then (\d+)", body)}
    full_floor = floors["completed"] | floors["conditional"]
    assert floors["completed"] == {(0,1,2,0,3,1):16,(0,1,2,3,0,4):16,(0,1,2,3,1,0):12,(0,1,2,3,1,4):16,(0,1,2,3,4,5):12}
    assert full_floor == {(0,1,2,0,3,1):16,(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,0,4):16,(0,1,2,3,1,0):12,(0,1,2,3,1,4):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
    specs = [("completed",483,551,"milestones/73-countfree-share-catalogue/data/proved-model.json", "milestones/73-countfree-share-catalogue/data/proved-potential.i64.gz",floors["completed"]),
             ("conditional_floor18",496,602,"milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18.json", "milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18-potential.i64.gz",full_floor)]
    profiles = {}
    for name, slope, limit, mr, pr, floor in specs:
        metadata = read(mr)
        buf = gzip.decompress(raw(pr))
        assert sha(buf) == metadata["potential_sha256"] and metadata["potential_range"] == limit
        pi = np.frombuffer(buf, dtype="<i8")
        assert len(pi) == 1601856 and int(pi.min()) == 0 and int(pi.max()) == limit
        profiles[name] = dict(pi=pi, P=slope, R=limit, floor=floor, potential_raw_sha256=sha(buf),
                              checked=0, minimum_slack=None, tight_edges=0, weight_hash=hashlib.sha256(),
                              saved_weight_hash=hashlib.sha256(), expected_saved_weight_sha256=metadata["weight_sha256"])
    old = "milestones/72-four-count-proof-closure/critical-current/"
    source_meta = read(old + "data/source-proved-model.json")
    source_file = ROOT / (old + "build/source-graph.npz")
    raw(old + "build/source-graph.npz")
    with np.load(source_file) as z:
        saved = {k:z[k] for k in z.files}
    assert len(saved["U"]) == 4947008
    assert {k:sha(v.tobytes()) for k,v in saved.items()} == source_meta["arrays_sha256"]
    assert set(dag["source_arrays_sha256"]) == {"direction","history","count_code"}
    assert all(sha(saved[k].tobytes()) == v for k,v in dag["source_arrays_sha256"].items())
    saved_keys = ((75*saved["direction"].astype(np.int64) + saved["history"])*46656 + saved["count_code"])
    assert np.all(saved_keys[1:] > saved_keys[:-1])
    codes = np.arange(46656, dtype=np.int64)
    digits = np.stack([codes//6**j % 6+1 for j in range(5,-1,-1)], axis=1)
    children = np.zeros((len(nodes)+2,7), dtype=np.int64)
    children[1] = 1
    children[2:] = nodes
    accepted = []
    class_counts = []
    for cls, root in enumerate(roots):
        state = np.full(46656, root, dtype=np.int64)
        for k in range(6):
            state = children[state, digits[:,k]]
        assert np.all((state == 0) | (state == 1)), cls
        take = codes[state == 1]
        accepted.append(take)
        class_counts.append(dict(class_id=cls,root=root,accepted_codes=len(take),codes_i64_sha256=sha(take.astype("<i8").tobytes())))
    sid = {tuple(s):i for i,s in enumerate(shapes)}
    key_hash = hashlib.sha256()
    extra_hash = hashlib.sha256()
    all_counts = Counter()
    extra_examples = []
    contexts = []
    violation = None
    for block, cls in blocks:
        di, qi = divmod(block,75)
        cs = accepted[cls]
        keys = block*46656 + cs
        key_hash.update(keys.astype("<i8").tobytes())
        low, high = np.searchsorted(saved_keys, [block*46656,(block+1)*46656])
        old_codes = saved["count_code"][low:high]
        is_saved = np.isin(cs,old_codes,assume_unique=True)
        missing = np.setdiff1d(old_codes,cs,assume_unique=True)
        all_counts.update(accepted=len(cs),saved_intersection=int(is_saved.sum()),extra=int((~is_saved).sum()),missing=len(missing))
        extra_hash.update(keys[~is_saved].astype("<i8").tobytes())
        if len(extra_examples) < 5:
            extra_examples += [dict(direction=di,history=qi,count_code=int(c),diagram_class=cls) for c in cs[~is_saved][:5-len(extra_examples)]]
        ds = extensions[di]
        a, rev = canon(ds[3:]), canon(ds[3:][::-1])
        shape = min(a,rev)
        syms = digits[cs]
        credit = np.full(len(cs), geometry[di], dtype=np.int64)
        for word, symbols, value in rules:
            hit = ((a == word) & (cs%7776 == enc(symbols))) | ((rev == word) & (cs%7776 == enc(symbols[::-1])))
            credit[hit] = np.maximum(credit[hit], value)
        emitted = tuple(prefixes[qi])+(di,)
        for sig,caps,geo,strong in histories:
            if len(emitted) < len(sig) or emitted[-len(sig):] != tuple(sig):
                continue
            np.maximum(credit,geo,out=credit)
            hit = np.ones(len(cs), dtype=bool)
            for k,cap in caps:
                hit &= syms[:,k] <= cap
            credit[hit] = np.maximum(credit[hit],strong)
        matches = [i for i,p in enumerate(prefixes) if p and len(p)<=len(emitted) and emitted[-len(p):]==tuple(p)]
        nq = max(matches,key=lambda j:len(prefixes[j])) if matches else 0
        ps,ts = sid[canon(ds[:8])],sid[canon(ds[1:])]
        u = (ps*7776 if qi==0 else 1026432+(qi-1)*7776)+cs//6
        v = (ts*7776 if nq==0 else 1026432+(nq-1)*7776)+cs%7776
        assert np.all(u<1601856) and np.all(v<1601856)
        assert len(missing)==0, ("saved keys missing",di,qi,missing[:5].tolist())
        assert np.array_equal(u[is_saved],saved["U"][low:high]) and np.array_equal(v[is_saved],saved["V"][low:high])
        block_stats = dict(direction=di,history=qi,diagram_class=cls,accepted=len(cs),saved=int(is_saved.sum()),extra=int((~is_saved).sum()))
        for name,p in profiles.items():
            weight = 120*(cs%6+1)+np.maximum(credit,p["floor"].get(shape,0))
            p["weight_hash"].update(weight.astype("<i8").tobytes())
            p["saved_weight_hash"].update(weight[is_saved].astype("<i8").tobytes())
            slack = weight+p["pi"][u]-p["pi"][v]-p["P"]
            p["checked"] += len(cs)
            ms = int(slack.min()) if len(cs) else None
            if ms is not None:
                p["minimum_slack"] = ms if p["minimum_slack"] is None else min(p["minimum_slack"],ms)
            p["tight_edges"] += int((slack==0).sum())
            block_stats[name+"_minimum_slack"] = ms
            if ms is not None and ms < 0:
                i = int(np.flatnonzero(slack<0)[0]); code = int(cs[i]); node=roots[cls]; trace=[node]
                for symbol in [code//6**j%6+1 for j in range(5,-1,-1)]:
                    node = node if node<2 else nodes[node-2][symbol]
                    trace.append(node)
                assert node == 1
                violation = dict(profile=name,direction=di,history=qi,count_code=code,diagram_class=cls,
                                 u=int(u[i]),v=int(v[i]),weight=int(weight[i]),P=p["P"],source_potential=int(p["pi"][u[i]]),
                                 target_potential=int(p["pi"][v[i]]),slack=int(slack[i]),present_in_saved_graph=bool(is_saved[i]),acceptance_trace=trace)
                assert violation["weight"]+violation["source_potential"]-violation["target_potential"]-violation["P"]<0
                break
        contexts.append(block_stats)
        if violation:
            break
    elapsed=time.monotonic()-start
    assert elapsed < 300, elapsed
    for name,p in profiles.items():
        if not violation:
            assert p["saved_weight_hash"].hexdigest()==p["expected_saved_weight_sha256"],name
    # Recheck immutable input bytes after all numerical work.
    assert all(sha((ROOT/rel).read_bytes())==digest for rel,digest in PINS.items())
    result=dict(status="COUNTEREXAMPLE_DEFINED_POTENTIAL" if violation else "PASS_ALL_DEFINED_GRAPH_POTENTIAL_INEQUALITIES",
                numerical_seconds=elapsed,defined_contexts=len(blocks),defined_classes=len(roots),diagram_nodes=len(nodes),
                checked_contexts=len(contexts),counts=dict(all_counts),saved_total=4947008,
                accepted_full_keys_i64_sha256=key_hash.hexdigest(),extra_full_keys_i64_sha256=extra_hash.hexdigest(),
                key_encoding="((75*direction)+history)*46656+count_code; lexicographic context/code order; little-endian int64",
                extra_examples=extra_examples,class_counts=class_counts,context_counts=contexts,violation=violation,
                profiles={name:{k:p[k] for k in ["P","R","potential_raw_sha256","checked","minimum_slack","tight_edges"]}|
                    dict(accepted_weight_i64_sha256=p["weight_hash"].hexdigest(),saved_weight_i64_sha256=p["saved_weight_hash"].hexdigest()) for name,p in profiles.items()},
                source_files_sha256=PINS,script_sha256=sha(Path(__file__).read_bytes()),
                actual_lean_diagram_literals_equal_dag_json=True,source_graph_endpoints_agree_on_intersection=True,
                scope="Independent exact integer enumeration of the defined graph with parsed Lean tables and source-inspected evaluators. No Lean certification, solver, compiler, new local refutation, or unconditional global snake bound.")
    (HERE/"data/defined-potential-audit.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:result[k] for k in ["status","numerical_seconds","checked_contexts","counts","profiles","violation"]},indent=2))

if __name__ == "__main__":
    main()
