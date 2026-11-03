"""Record checked counterexamples and the unfinished geometric proof separately."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
for name in ['Witness133','BalancedWitness133','IntervalPacking133','OccurrenceArithmetic133']:
 assert read(H/'data'/(name+'-audit.json'))['status']=='PASS'
geometry=read(H/'data/occurrence-geometry.json')
assert geometry['result']['one_endpoint_max']==12 and not geometry['result']['lean_checked']
update='''# Research update: milestone 133

Two concrete counterexamples have passed Lean. A149-edge odd snake attains
pair counts6 and3 in a canonical012032 window. A133-edge odd snake attains
counts4 and5. Thus the pair floor cannot be raised uniformly to ten, even
when both counts are at least four. These are auxiliary sharpness examples,
not improvements on the191-edge construction or realizations of a full
periodic critical cycle. Neither example decides a length235-only restriction.

The first witness's window starts130 edges after its qualifying endpoint.
The second is106 edges from its qualifying final endpoint. Hamming proximity
therefore cannot be replaced by a short distance along the path.

A written geometric argument bounds the number of assigned windows at one
endpoint by twelve, or eleven when no counted window includes that endpoint.
It uses the common coordinate in the alternating window vertices and the
absence of the opposite pair between consecutive such vertices. The interval
packing lemma and final conditional arithmetic have passed Lean. The transfer
from an actual snake to the full geometric counting argument remains pending;
the occurrence theorem itself is not yet Lean-checked.

The endpoint0 search returned native UNSAT with no cycle cuts. Its exclusion
has no checked certificate and must not be used as a theorem. The other two
searches produced the fully checked witnesses. All inputs, models, valid cuts,
native reviews, compiler attempts and successful receipts are retained.

Next selected task: complete the actual-snake geometric occurrence proof.
Do not replace it by another uniform pair-floor proposal. The recorded global
interval remains191–235 with the existing incomplete independent upper-proof
rebuild; the optimum and196 remain open. Paper revision126 remains unchanged,
with the next full revision due at136. Only notation needed repeatedly in
the counting proof is introduced.

'''
for a,b in [('A149','A 149'),('A133','A 133'),('counts6','counts 6'),('and3','and 3'),
 ('canonical012032','canonical 012032'),('counts4','counts 4'),('and5','and 5'),
 ('the191','the 191'),('length235','length 235'),('starts130','starts 130'),
 ('is106','is 106'),('endpoint0','endpoint 0'),('remains191','remains 191'),
 ('and196','and 196'),('revision126','revision 126'),('at136','at 136')]:update=update.replace(a,b)
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
 'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8-sig');assert not old.startswith('# Research update: milestone 133')
 p.write_text(update+'## Earlier record\n\n'+old,encoding='utf-8',newline='\n')
note=r'''# Sharpness and the number of endpoint exceptions

## Two counterexamples checked in Lean

Both examples contain the window

\[
(0,1,3,7,6,14,10),
\]

whose transition sequence is \(012032\).

| Example | Edges | Window start | Five internal counts | Relevant pair | Qualifying endpoint |
|---|---:|---:|---|---|---|
| First | 149 | 130 | \((8,6,10,3,8)\) | \(6+3=9\) | Initial vertex18 |
| Balanced | 133 | 27 | \((11,4,13,5,12)\) | \(4+5=9\) | Final vertex130 |

The first snake has endpoints18 and13; only18 is at distance two from both
counted centres. The second has endpoints25 and130; only130 has the two
required distances. The first qualifying window begins130 edges from the
corresponding endpoint. In the second example, the corresponding endpoint is
106 edges after the window begins. These examples exclude an inference from
Hamming distance two to a short segment along the path.

The complete vertex sequences, induced-path condition, canonical shape,
individual pair counts and endpoint distances have passed Lean. The final
negative statements explicitly refute the following proposed strengthenings:

1. Every fitting \(012032\) window has pair sum at least ten.
2. Every fitting \(012032\) window whose two counts are at least four has
   pair sum at least ten.

Both examples have odd length. Their complete five-count vectors differ from
the vectors in the surviving periodic critical cycle. They therefore establish
local sharpness of the pair conditions and do not realize that entire cycle.
They also leave restrictions specifically to length235 open. Neither example
improves the recorded191-edge construction.

The search with the first window vertex required to be an endpoint returned
native UNSAT in0.547 seconds, without any model or added cycle cut. This has
no checked contradiction certificate. The other searches produced the149-edge
and133-edge paths in2.688 and4.937 seconds, respectively, after adding valid
cycle cuts. No inference from a timeout or a disconnected model is used.

## Counting occurrences using the actual endpoint

The new written argument gives at most twelve assigned windows per endpoint,
or eleven when no counted window has that endpoint as its boundary. Each
window is assigned to one endpoint at distance two from both counted centres.
The argument applies to this larger geometric class; the pair-at-most-nine
condition supplies the assignment through the completed milestone132 theorem.

The full proof is in audit/occurrence-geometry.md. Its essential steps are:

1. Orient the path from the endpoint and translate it to zero. The first
   neighbour forbids all but one selected distance-two vertex containing its
   coordinate. The remaining selected vertices correspond to pairs among
   eight coordinates.
2. The four alternating positions of each assigned window share one coordinate.
   When the endpoint is a window boundary, include it as the initial element.
   Intervals sharing different coordinates can overlap in at most one position.
3. Consecutive pairs \(\{u,v\}\) and \(\{u,w\}\) force \(\{v,w\}\) to
   be absent. Otherwise the intervening triple has three selected neighbours.
4. Count the available pairs and the missing pairs along these intervals.
   The two resulting inequalities leave one exceptional integer case,
   \((a,k,t)=(5,5,3)\). A missing-degree count excludes that case.

Here \(a\) counts the common coordinates used, \(k\) counts the maximal
intervals, and \(t\) counts missing pairs incident to those coordinates.
These quantities are used repeatedly in the proof and are unnecessary outside
that argument. With \(\delta=1\) for a counted boundary window and zero
otherwise, the conclusion of the written argument is \(W\le11+\delta\).

The following parts have passed Lean:

- The interval inequality
  \[
  |I|+2|\{\text{labels used by }I\}|+1
  \le\left|\bigcup_{r\in I}\{r,r+1,r+2,r+3\}\right|,
  \]
  under the stated separation between differently labelled starts.
- The earlier numerical estimate sixteen from that inequality and the pair
  capacity.
- The exceptional-case arithmetic and the conclusion \(W\le11+\delta\),
  conditional on the two geometric estimates and the exceptional-case estimate.

The complete occurrence theorem for actual snakes has not yet been checked
in Lean. Its remaining obligations are the coordinate-pair representation,
the construction of the intervals, the missing-pair argument, the path-block
count and their combination with the checked arithmetic. The bound twelve
must retain this verification status in summaries and the paper.

The written proof would give at most24 low-pair windows after choosing one
qualifying endpoint for each start. A reduction to22 would additionally require
excluding counted boundary windows at both ends. The native endpoint0 result
is insufficient for that deduction. Neither budget is currently a completed
Lean theorem about actual snakes.

## Consequences for the length problem

The counterexamples show why occurrence restrictions are needed. The two
surviving cycle constraints from milestone132 still limit the uniform-credit
formula, even after an occurrence allowance is supplied. Additional restrictions
or a revised comparison will be needed before any new length bound is claimed.

The recorded interval remains191–235, with its documented independent-rebuild
limitation. The value196 and optimality remain unresolved. The selected next
task is the actual-snake transfer for the occurrence argument. The paper remains
at revision126; its next scheduled full revision is136.
'''
for a,b in [('vertex18','vertex 18'),('vertex130','vertex 130'),('endpoints18','endpoints 18'),
 ('endpoints25','endpoints 25'),('and13','and 13'),('and130','and 130'),('only18','only 18'),
 ('only130','only 130'),('begins130','begins 130'),('length235','length 235'),('recorded191','recorded 191'),
 ('in0.547','in 0.547'),('the149','the 149'),('and133','and 133'),('in2.688','in 2.688'),
 ('and4.937','and 4.937'),('milestone132','milestone 132'),('most24','most 24'),
 ('to22','to 22'),('endpoint0','endpoint 0'),('remains191','remains 191'),('value196','value 196'),
 ('revision126','revision 126'),('is136','is 136')]:note=note.replace(a,b)
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
(H/'README.md').write_text(update.replace('# Research update: milestone 133','# Milestone 133: sharpness and endpoint occurrences',1)+'''## Saved material

- MATHEMATICAL_NOTE.md separates proved counterexamples from the written count.
- lean/Witness133.lean and BalancedWitness133.lean contain the two checked paths.
- work/probe-endpoint18 and work/probe-balanced retain all models and reviews.
- work/probe-endpoint0 retains the uncertified boundary exclusion result.
- audit/occurrence-geometry.md contains the written geometric proof.
- lean/IntervalPacking133.lean and OccurrenceArithmetic133.lean contain the
  checked general and conditional lemmas.
- data/*-audit.json records successful compiler runs and exact dependency hashes.
- data/verification.json, checkpoint.json and file-manifest.json fix this save.

Do not restart completed probes or checks. The separate milestone115 proof job
must be inspected through its live process and lock before any restart.
''',encoding='utf-8',newline='\n')
prompt='''# Continuation after milestone 133

Work in E:/Snake-in-a-box. Use the requested research skill, preserve the
three authors and hyperlink settings, and introduce only essential repeated
notation. Fetch GitHub each round. Leave unrelated .gitignore and milestone50
changes intact. Preserve exact audited files, failures and live proof jobs.

The previous round made concrete progress: two actual counterexamples and
four general/conditional lemmas passed Lean. Read the milestone133 mathematical
note, occurrence-geometry audit and compiler receipts. Do not rerun the probes.

The149-edge witness has window start130 and pair6+3; the133-edge witness has
start27 and pair4+5. Both are odd snakes with exact canonical012032 windows.
Thus uniform pair10 is false, including the version requiring both counts>=4.
The full five-count contexts differ from the critical periodic cycle, and a
restriction specifically to length235 remains open. Neither path is a new
record. The endpoint0 probe is native UNSAT without a checked certificate.

NEXT SELECTED TASK: complete the geometric occurrence proof in Lean. The
written argument gives at most12 assigned windows per endpoint, or11 without
a counted boundary window. This is not yet a checked actual-snake theorem.
The interval-union lemma and integer reduction are already checked; do not
replace the required geometric transfer with more conditional arithmetic.

Normalize one endpoint and its first two steps. Selected distance-two vertices
are K8 coordinate pairs plus one exceptional pair. Each assigned012032 window
has four alternating positions sharing one coordinate, with a virtual endpoint
only at a counted boundary. Construct the maximal intervals and their overlap
count. Consecutive pairs uv,uw force vw absent; prove the missing-edge path-block
bound. In notation from the audit, the two estimates are
W<=7a-a(a-1)/2-t-2k+delta and
W<=k(5-a+t)-t+1+delta for a<=7.
Assuming W>=12+delta leaves a=k=5,t=3; the degree count gives
W+3k<=6a-4+delta. Those integer implications passed Lean. Handle a=8 separately
by the absence of missing pairs, as the audit explains. Finish the actual
one-endpoint theorem, then combine endpoint groups with milestone132.

Keep the written24 total budget distinct from a completed Lean statement.
The proposed22 budget would additionally need certified boundary exclusions.
The old thirteen-window theorem requires BOTH endpoints and is not used here.
The uniform-credit limitation from132 remains relevant; an occurrence budget
alone does not prove a smaller global length bound.

Global recorded interval191–235; independent contributor upper-proof rebuild
incomplete; optimum and196 open. Paper revision126 unchanged, next revision136.
Check the saved batch observation and live milestone115 driver before action.
'''
for a,b in [('milestone50','milestone 50'),('milestone133','milestone 133'),('The149','The 149'),
 ('start130','start 130'),('pair6+3','pair 6+3'),('the133','the 133'),('start27','start 27'),
 ('pair4+5','pair 4+5'),('canonical012032','canonical 012032'),('pair10','pair 10'),
 ('length235','length 235'),('endpoint0','endpoint 0'),('most12','most 12'),('or11','or 11'),
 ('assigned012032','assigned 012032'),('milestone132','milestone 132'),('written24','written 24'),
 ('proposed22','proposed 22'),('from132','from 132'),('interval191','interval 191'),
 ('and196','and 196'),('revision126','revision 126'),('revision136','revision 136'),
 ('milestone115','milestone 115')]:prompt=prompt.replace(a,b)
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8',newline='\n')
print('Saved counterexamples, written occurrence proof status and continuation.')
