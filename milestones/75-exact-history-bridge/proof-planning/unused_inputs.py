"""Read-only measurement of unused initial clauses in the selected RUP proof."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7305'
selection=json.loads((CASE/'data/lrat-slice-selection.json').read_text())
with (CASE/'certificates/share7305.cnf').open() as stream:
    header=next(line.split() for line in stream if line.startswith('p cnf'))
n=int(header[3]);used=set();derived=0;hint_count=0;digest=hashlib.sha256()
with (CASE/'certificates/share7305.lrat').open('rb') as stream:
    for line in stream:
        digest.update(line);words=line.split()
        if not words or words[1]==b'd':continue
        split=words.index(b'0',1);hints=list(map(int,words[split+1:-1]))
        assert words[-1]==b'0' and all(h>0 for h in hints)
        derived+=1;hint_count+=len(hints)
        used.update(h for h in hints if h<=n)
assert digest.hexdigest()==selection['selected_lrat_sha256']
assert derived==selection['after']['lemmas'] and hint_count==selection['after']['hints']
unused=n-len(used);predicted=max(n,selection['after']['slots']-unused)
out=dict(status='READ_ONLY_SLOT_PLANNING',input_clauses=n,used_input_clauses=len(used),
         unused_input_clauses=unused,current_slots=selection['after']['slots'],
         predicted_slots_if_unused_inputs_released=predicted,
         predicted_word_width=predicted.bit_length(),derived_clauses=derived,hints=hint_count,
         lrat_sha256=digest.hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         scope='Read-only count. The slot estimate assumes immediate reuse of unused initial clauses. No exporter change, simulation, selected-proof mutation, speed measurement or Lean theorem is supplied.')
(HERE/'data').mkdir(exist_ok=True)
(HERE/'data/unused-inputs.json').write_text(json.dumps(out,indent=2)+'\n')
print(out,flush=True)
