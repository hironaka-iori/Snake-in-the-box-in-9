"""Add the checked conditional refinement without asserting its missing premises."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]

def main():
    q=json.loads((H/'data/remainder-completion.json').read_text())
    assert q['status']=='PASS_RETAINED_CORNER_LOSS_ARITHMETIC' and q['statements']==7
    assert not q['positive_loss_bound_proved'] and not q['new_full_graph_potential_proved']
    assert not q['new_unconditional_bound']
    paragraph='''Seven additional arithmetic statements passed Lean. Retaining the existing
corner-share loss subtracts five times that loss from the comparison
numerator. At mean4462/9, range601 and correction0, an integer loss of at
least4 crosses the strict235 threshold. The packing and potential premises
remain explicit. Neither a positive global loss bound nor a compatible
full-graph potential was proved. Read
milestones/163-share18-replay-continuation/ROUNDING_LOSS.md and its adjacent
data/remainder-completion.json. This is a conditional refinement; the
unconditional numerical bound is unchanged.

'''
    for rel in ['README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']:
        p=R/rel;b=p.read_bytes();marker=b'Last full paper revision:156; next:166.'
        assert marker in b
        if paragraph.encode() not in b:b=b.replace(marker,paragraph.encode()+marker,1)
        p.write_bytes(b)
    addendum='''
## Checked retained-loss arithmetic

Seven statements passed in the narrow-import retry. Read ROUNDING_LOSS.md
and data/remainder-completion.json for the exact inequality and its scope.
The fixed-parameter integer threshold is4; a loss of3 leaves the comparison
above235. The conditional edge bound234 requires the explicit packing,
exact-budget, potential and positive-loss hypotheses.

The first arithmetic attempt stopped at the free-memory reserve before
acceptance. Its source, plan and failure record remain preserved. The
successful retry changes only the imports; its proof body is byte-identical.
Use data/remainder-execution-v2.json and the accepted V2 module receipt.
The original failed attempt is not an accepted theorem package.

The scale review also checks the rounding convention and the edge-versus-
vertex conversion. The saved local/global share identification was already
checked in milestone73; its source and object were rehashed against the
saved receipt here. No transitive dependency rebuild was claimed for that
historical identification. See review/core-share-identification.json.

Continue the share18 contradiction replay as the primary task. The
retained-loss result identifies an additional conditional possibility;
its positive-loss and full-potential requirements are still unresolved.
'''
    p=H/'COMPLETION.md';b=p.read_bytes()
    if addendum.encode() not in b:p.write_bytes(b+addendum.encode())
    print('RECORDED_SEVEN_CHECKED_CONDITIONAL_STATEMENTS')

if __name__=='__main__':main()
