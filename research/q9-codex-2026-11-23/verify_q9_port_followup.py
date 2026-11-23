"""Cross-check parity split coverage, independently validate witnesses and identify known classes."""
import gzip
import json
from collections import Counter, defaultdict
from pathlib import Path
from verify_q9_center_avoidance import code, verify

def path_form(p):
    verify(p)
    assert len(p) == 192
    return code([a ^ b for a, b in zip(p, p[1:])])

def rows(file):
    return [json.loads(line) for line in Path(file).read_text().splitlines()]

def verify_searches():
    first = rows("q9_port_radius5_pairs.jsonl")
    initial = {i: status for i, _, status, *_ in first if i != "control"}
    remaining = {i for i, s in initial.items() if s == "UNKNOWN"}
    assert len(initial) == 260 and len(remaining) == 98
    assert set(initial.values()) == {"UNKNOWN", "UNSAT"}
    second = rows("q9_port_five_color_retry.jsonl")
    path_form(second[0][-1])
    assert second[0][:2] == ["control","FOUND"]
    assert len(second[1:]) == 196
    assert {(i, mode, status) for i, mode, status, *_ in second[1:]} == {
        (i, mode, "UNSAT") for i in remaining for mode in (0,1)}
    radius4 = rows("q9_port_radius4_supports.jsonl")
    assert {r[0] for r in radius4 if r[2]=="UNSAT"} == set(initial)
    for name in ("q9_two_windows_control.log","q9_two_windows_cross_control.log","q9_armtips_191_control.log","q9_mutable_arm_join_control.log"):
        fields = Path(name).read_text().split()
        assert fields[0] == "FOUND"
        path_form(list(map(int,fields[1:])))
    with gzip.open("q9_port_followup_public191.txt.gz","rt") as stream:
        public={path_form(list(map(int,s.split()))) for s in stream}
    found=set()
    for line in Path("q9_mutated_armtips_178.log").read_text().splitlines():
        fields=line.split()
        if fields[0]=="PATH191":
            shape=path_form(list(map(int,fields[1:])))
            assert shape not in found
            found.add(shape)
        if fields[0]=="FOUND":
            answer=list(map(int,fields[1:]));verify(answer);assert len(answer)>=193
    assert len(public)==131
    return dict(single_chord_inputs=260,radius5_previously_unresolved=len(remaining),
                radius5_split_UNSAT=len(second)-1,public_bank=len(public),
                constructed_191=len(found),outside_public_191=len(found-public))

if __name__=="__main__":
    print(json.dumps(verify_searches(),indent=2))
