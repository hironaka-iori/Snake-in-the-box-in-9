"""Merge search results by rooted projection, keeping unknowns reproducible."""
from collections import Counter
from pathlib import Path
import json
sources={
 "three_axes_from_records":[
     "q9_cube_fiber_final_192.jsonl","q9_three_axis_strip_192.jsonl","q9_three_axis_reverse_192.jsonl"],
 "one_extra_contact":[
     "q9_extended_projection_192.jsonl","q9_extended_projection_remaining_one_192.jsonl",
     "q9_extended_projection_deep_192.jsonl","q9_extended_projection_reverse_192.jsonl"],
 "two_extra_contacts":[
     "q9_extended_projection_two_contacts_192.jsonl","q9_extended_two_deep_192.jsonl"],
 "interior_detours":["q9_projected_detour_192.jsonl"],
 "four_axes_from_records":["q9_four_axis_first_192.jsonl"],
}
def summary(fs):
    cases={};wins={}
    for fname in fs:
        for row in map(json.loads,Path(fname).read_text().splitlines()):
            status,base,*rest=row
            if cases.get(base) in ("FOUND","UNSAT") and status not in ("UNKNOWN",cases[base]):
                raise ValueError((fname,base,"inconsistent results"))
            if cases.get(base,"UNKNOWN")=="UNKNOWN":cases[base]=status
            if status=="FOUND":wins[base]=rest[-1]
    retry = "q9_free_fiber_glue_retry_192.jsonl"
    retried = []
    for status, base, witness, origin in map(json.loads, Path(retry).read_text().splitlines()):
        if origin not in fs:
            continue
        retried.append(base)
        previous = cases[base]
        if previous == "UNKNOWN":
            cases[base] = status
        elif status not in ("UNKNOWN", previous):
            raise ValueError((origin, base, "inconsistent retry"))
        if status == "FOUND":
            wins[base] = witness
    if retried:
        fs = [*fs, retry]
    return {"counts":dict(Counter(cases.values())),"unresolved":[p for p,s in cases.items() if s=="UNKNOWN"],"witnesses":wins,"sources":fs}
if __name__=="__main__":
    print(json.dumps({label:summary(fs) for label,fs in sources.items()},indent=2))
