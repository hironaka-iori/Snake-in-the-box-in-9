"""State the full finite-graph result and the next falsifiable hypothesis."""
from pathlib import Path
from fractions import Fraction
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result=read(H/'data/odd-pair9-six25/results.json')
review=read(H/'data/graph-review.json')
screen=read(H/'data/endpoint9-witness-screen.json')
assert result['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
assert review['status']=='PASS_STATIC_AND_INDEPENDENT_SAVED_CYCLE_REVIEW'
assert screen['pair9_windows_checked']==0 and screen['qualifying_window_screen_is_vacuous']
assert [p['mean'] for p in result['profiles']]==['488','496']
assert [p['comparison_integer_bound'] for p in result['profiles']]==[235,234]
update=r'''# Research update: milestone 131

The full graph comparison has completed. Adding the proved odd-length pair
bound nine and the proposed 0123104 six-count bound twenty-five raises the
first profile's minimum from 2915/6 to 488. Its integer comparison remains
235. The additional-share profile retains minimum 496 and its previous
integer comparison 234. Both profiles still contain unproved hypotheses;
these are finite-model comparisons, with no new bound for actual snakes.

The new attaining cycles avoid 0123104. Raising only that proposed bound
above twenty-five therefore cannot improve either minimum in this model.
The existing potentials remain valid as weights increase or edges disappear,
and the same unaffected cycles attain equality. Even zero potential range
would leave the comparisons above 235 and 234, respectively. This rules out
further progress toward 234/233 by strengthening only that pattern.

The first profile's four-edge cycle consists entirely of 0120324 windows
up to reversal, with relevant pair sums exactly nine. This identifies the
next question: for an odd-length snake, does a fitting 012032 window with
pair sum nine force one endpoint to be at Hamming distance two from both
counted centres? This is a hypothesis. A screen of 133 validated saved snakes
found 54 relevant windows and no pair-sum-nine window, so it gives no evidence
for or against the hypothesis.

The evaluator checked every retained-edge potential inequality; the
independent review reconstructed the saved cycles from original graph rows
and checked their weights, adjacency and zero slacks. It did not repeat the
full all-edge calculation. No new Lean theorem is claimed in this round.
The next selected task is a direct counterexample search for the odd-length
endpoint statement, followed by a checked certificate if the search is negative.

The maintained interval remains 191–235, with the documented incomplete
independent rebuild of the contributor upper-bound proof. The optimum and
196 remain open. Existing notation is retained. Paper revision 126 is
unchanged; the next scheduled full revision is 136.

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
             'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8-sig')
 assert not old.startswith('# Research update: milestone 131')
 p.write_text(update+'## Earlier record\n\n'+old,encoding='utf-8',newline='\n')
note=r'''# What the full comparison changes

The experiment uses the proved pair bound nine for odd-length snakes and a
proposed six-count lower bound twenty-five for direction shape 0123104.
The previous removal list and both complete weight vectors were reproduced
before applying the new constraints. The resulting graph has 1,601,856 states
and 4,661,773 retained edges. The pair condition removes 14,771 edges, and the
six-count condition removes another 6,570.

## Exact finite-model results

| Profile | Previous minimum | New minimum | Previous comparison | New comparison |
|---|---:|---:|---:|---:|
| Completed share catalogue | \(2915/6\) | \(488\) | \(1324108/5623\) | \(1103449/4688\) |
| Additional share assumptions | \(496\) | \(496\) | \(551765/2348\) | \(551765/2348\) |

The first comparison is approximately 235.37735; the second is approximately
234.99361. Their integer parts remain 235 and 234. The first profile's name
refers to its share catalogue. Its inherited count-sum hypotheses remain
unproved, and the proposed six-count inequality is also unproved.

The evaluator verifies integer-potential inequalities on every retained edge
and a closed cycle attaining each minimum. The independent review reconstructs
both cycles from the original graph rows, checks their weights and adjacency,
and checks the full saved potential hashes and ranges. It does not repeat the
full all-edge calculation. These are exact native finite-model results; the
complete Lean graph verification and transfer to arbitrary snakes remain open.

## Why the selected pattern cannot give further progress alone

The cycles attaining 488 and 496 avoid 0123104. Increasing its proposed bound
from twenty-five upward can only increase some weights and delete some edges.
Thus the existing potential inequalities remain valid. The two displayed
cycles remain present with unchanged weights, so they still attain the same
minima. This conclusion concerns this fixed finite model and this single
change to its assumptions.

Even an ideal potential range of zero would give

$$
\frac{68929}{293}=235+\frac{74}{293}>235,
\qquad
\frac{137866}{587}=234+\frac{508}{587}>234.
$$

Consequently, strengthening only this pattern cannot produce the next integer
comparisons 234 and 233 through the existing formula. The elementary
monotonicity deduction is written and independently reviewed; it is not a
new Lean-certified assertion about arbitrary snakes.

## The remaining four-edge cycle

All four seven-direction windows have canonical shape 0120324 after allowing
reversal. Counts below are put in that canonical orientation; all are exact.

| Edge | Six counts | Total | Second plus fourth |
|---|---|---:|---:|
| 2222328 | \((4,5,3,4,4,5)\) | 25 | 9 |
| 147674 | \((4,4,3,5,4,4)\) | 24 | 9 |
| 2220858 | \((3,4,4,5,3,4)\) | 23 | 9 |
| 146782 | \((3,5,4,4,3,5)\) | 24 | 9 |

The fourth count is four or five, so the completed fourth-count-three theorem
does not apply to these windows. Each relevant pair attains the new lower
bound nine. A restriction on how often this equality occurs could therefore
address this cycle. No actual snake realizing the cycle has been constructed.

The other profile's seven-edge cycle has no matching 012032 pair window. Its
seven-direction shapes are 0123045, 0123014 and 0123042. The proposed endpoint
test therefore addresses the first obstruction only.

## Next hypothesis and its first test

For odd \(m\), consider the following implication in a fitting 012032 window:

$$
\alpha_{r+2}+\alpha_{r+4}=9
\quad\Longrightarrow\quad
\exists e\in\{0,m\},\quad
d_H(p_{r+2},p_e)=d_H(p_{r+4},p_e)=2.
$$

This remains a hypothesis. The two centres have the same parity, while an
odd-length snake has endpoints of opposite parity. Hence at most one endpoint
can satisfy the displayed conclusion. If the implication holds, repeated
equality windows could be counted through the vertices at distance two from
the two endpoints. No occurrence bound from this hypothesis is yet claimed.

A cheap screen independently validated 133 distinct saved vertex sequences,
including the explicit 191-edge construction, a bank of 131 snakes, and a
120-edge endpoint witness. All 54 matching windows had pair sums different
from nine. The test is therefore vacuous for the implication; absence of a
counterexample here supplies no supporting evidence.

The selected next test normalizes the window to
\((0,1,3,7,6,14,10)\), retains the multiplicity of the 42 opposite-corner
occurrences, imposes pair sum at most nine, and requires an endpoint of each
vertex parity. It forbids endpoint flags at the fourteen vertices that are
at distance two from both 3 and 6. A genuine path satisfying this input would
refute the hypothesis. A negative native search would still require a complete
certificate and an actual-snake interpretation. Disconnected cycle components
must be excluded by valid cycle cuts before a selected set is called a path.

No new definition is introduced. The global interval and its independent-proof
limitation are unchanged. The paper is at revision 126; its next full revision
is due at 136.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
readme=update.replace('# Research update: milestone 131','# Milestone 131: the full comparison and its remaining cycles',1)
readme+='''## Saved evidence

- MATHEMATICAL_NOTE.md gives the numerical comparisons and the next hypothesis.
- data/odd-pair9-six25/results.json records the exact finite-model results.
- The same directory contains both potentials, cycles, source snapshot and logs.
- audit/graph-review.md distinguishes the evaluator's all-edge check from the
  independent reconstruction of the saved cycles.
- audit/endpoint9-witness-screen.md records the vacuous saved-witness screen.
- data/next-endpoint-task.json specifies the selected counterexample query.
- data/batch-observation.json records the other proof jobs at checkpoint time.
- data/verification.json, data/checkpoint.json and data/file-manifest.json
  identify the exact saved scope and bytes.

The historical preparation and low-memory observation remain unchanged. The
later launch record confirms that both resource gates passed and the full
calculation completed. The transient first GitHub refresh failure was resolved
on retry. A Git commit-graph warning did not prevent retrieval of the pinned
historical graph algorithm.

Do not rerun the completed graph or overwrite the original attempt. Any new
experiment must have a distinct label and preserve the existing evidence.
The milestone 115 proof job is separate and pending; inspect its process and
lock before any restart. Milestone 104 remains stopped after its timeouts.
'''
(H/'README.md').write_text(readme,encoding='utf-8',newline='\n')
task=dict(status='PROPOSED_ODD_PAIR9_ENDPOINT_COUNTEREXAMPLE_QUERY',
 directions=[0,1,2,0,3,2],normalized_window=[0,1,3,7,6,14,10],centres=[3,6],
 count_positions=[1,3],pair_sum_cap=9,corner_occurrences=42,preserve_multiplicity=True,
 endpoint_conditions=['At least one even-parity endpoint','At least one odd-parity endpoint',
 'No endpoint at distance two from both centres'],
 common_vertices=[v for v in range(512) if (v^3).bit_count()==(v^6).bit_count()==2],
 actual_statement='For odd-length actual snakes, pair sum9 in fitting012032 forces one endpoint at distance2 from both centres.',
 hypothesis_proved=False,known_witness_screen_vacuous=True,
 source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [
 H/'data/odd-pair9-six25/results.json',H/'data/graph-review.json',H/'data/endpoint9-witness-screen.json',
 R/'milestones/130-fourth-count-large/data/odd-pair-verification.json']},
 next_action='Run one bounded full-cube counterexample search, independently validate any returned path, and otherwise retain the native result as uncertified until complete replay and semantic transfer.',
 scope='Selected next question, not a theorem or numerical bound.')
assert len(task['common_vertices'])==14
(H/'data/next-endpoint-task.json').write_text(json.dumps(task,indent=2)+'\n',encoding='utf-8')
prompt='''# Continuation after milestone 131

Work in E:/Snake-in-a-box. Use the requested research skill. Keep ordinary
notation and define only essential quantities used repeatedly. Preserve the
authors, hyperlink settings, unrelated .gitignore and milestone 50 edits, and
live proof jobs. Fetch GitHub with automatic maintenance disabled.

Read milestones/131-odd-pair-six-count/MATHEMATICAL_NOTE.md and the graph and
endpoint-witness reviews. The full graph experiment has completed. Do not
restart it. First profile mean488, range585, comparison1103449/4688; additional
share profile mean496, range602, comparison551765/2348. Integer comparisons
remain235 and234 under inherited unproved hypotheses. The second is unchanged
from121. This is no new actual-snake bound.

Both attaining cycles avoid0123104. Raising only its floor above25 preserves
both minima, and even zero potential range cannot reach234/233. Stop pursuing
that single-pattern strengthening as a sufficient numerical route.

NEXT SELECTED TASK: test the odd-length pair9 endpoint hypothesis specified
in data/next-endpoint-task.json. The first profile's four-edge cycle consists
entirely of0120324 windows up to reversal, with exact pair9 and fourth4or5.
Test whether a fitting012032 pair9 window in an odd-length snake forces one
endpoint at Hamming distance2 from both centres. This is currently unproved.
The133 validated saved snakes contain54 matching windows but no pair9 window;
that screen is vacuous, not support for the hypothesis.

Normalize to vertices0,1,3,7,6,14,10. Count42 corner occurrences with their
multiplicity and impose cap9. The existing encoding allows at most2 endpoint
flags. Add a positive clause over even-parity endpoint flags and another over
odd-parity flags; these force one of each. Forbid all14 endpoint flags at
distance2 from both3 and6. Both endpoint clauses and all forbidden units need
separate Lean semantic justification if a negative search is promoted to proof.
Use122 endpoint encodings and the existing count semantics as references.

Start with a bounded native falsification search. Reject disconnected cycle
components through validated cuts. Independently validate any returned path,
its odd length, the fitting window, exact counts and endpoint distances.
An UNSAT or timeout without a complete checked certificate proves no theorem.
If a refutation is found, inspect its used premises: it may prove a stronger
claim if some endpoint restrictions are unused. Preserve exact traces and
every failed attempt; do not duplicate active processes.

The completed130 statements remain available: pair8 forces even length and
even start; fourth3 in0120324 gives triple>=12 and six>=23. The complementary
fourth>=4 case remains open. Milestone115 is pending and104 stopped; inspect
current processes. The maintained interval is191–235 with the contributor
upper-proof independent-rebuild limitation. The optimum and196 are unresolved.
The goal remains active. Paper126 is unchanged; full revision next136. Keep
the D: editor and E: paper mirror. No successful PDF compilation was established
after the earlier split-root Windows token failure. Commit and verify a remote
checkpoint after each completed round.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8',newline='\n')
print('Saved full-model result, limitation, and selected falsification task.')
