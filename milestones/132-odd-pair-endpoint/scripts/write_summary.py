"""Publish the local result only after the complete Lean assembly passes."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/replay-progress.json')['status']=='PASS_COMPLETE_CNF_REFUTATION'
for name in ['ActualCounters132','CoreSemantics132','ActualEndpoint132']:
 assert read(H/'data'/(name+'-audit.json'))['status']=='PASS'
assert read(H/'data/independent-credit-audit.json')['status']=='PASS'
assert (H/'data/endpoint-export-review.json').exists()
update=r'''# Research update: milestone 132

A new local theorem has passed the complete Lean check. In any snake in Q9,
a fitting canonical 012032 window with second-plus-fourth internal count at
most nine forces one endpoint to be at Hamming distance two from both counted
centres. There is no length-parity assumption. Consequently the pair sum is
at least ten whenever neither endpoint has those two distances.

The proof includes all 51 certificate modules, the interpretation of all 683
selected clauses for an actual snake, and the final coordinate transfer.
It preserves the 42 corner occurrences, including five vertices counted twice.
The final statements use only the standard Lean axioms recorded in their logs.
The two failed semantic attempts and the successful checks are saved.

This is an unconditional local result. It supplies no new global upper bound.
The maintained interval remains 191–235, with the documented incomplete
independent rebuild of the contributor upper-bound proof. The optimum and
the proposed value 196 remain unresolved.

A separate Lean-checked arithmetic result limits the current uniform-credit
approach. The two surviving cycle constraints keep its comparison above 235
when the endpoint-event allowance is at least two. This limitation concerns
the stated fixed model and formula. It does not rule out sharper geometric
restrictions or a revised graph that excludes other surviving cycles.

Next: use the endpoint theorem to study how low-pair windows can occur along
one actual snake. The earlier bound of thirteen windows requires proximity
to BOTH endpoints and cannot be reused for this one-endpoint conclusion.
Retain the seven-edge competing cycle when testing any proposed improvement.
No new mathematical definition is introduced. Paper revision 126 is unchanged;
the next scheduled full paper revision is136.

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
 'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8-sig')
 assert not old.startswith('# Research update: milestone 132')
 p.write_text(update+'## Earlier record\n\n'+old,encoding='utf-8',newline='\n')
note=r'''# Endpoint consequence of a small pair sum

Let \(p_0,\ldots,p_m\) be a snake in \(Q_9\), with the existing internal
counts \(\alpha_i\). Suppose \(r+6\le m\) and the six directions beginning
at \(r\) have canonical form \(012032\).

## Checked theorem

\[
\alpha_{r+2}+\alpha_{r+4}\le9
\quad\Longrightarrow\quad
\exists e\in\{0,m\},\qquad
d_H(p_{r+2},p_e)=d_H(p_{r+4},p_e)=2.
\]

The same endpoint satisfies both equalities. No parity restriction on
\(m\) or \(r\) is required. In particular, if neither endpoint satisfies
the two equalities, then

\[
\alpha_{r+2}+\alpha_{r+4}\ge10.
\]

This strengthens the previous unconditional local floor eight and the
odd-length floor nine in the stated geometric situation. It does not assert
that every fitting window has pair sum at least ten.

## Proof and verification

Translate the initial window vertex to zero and permute the coordinates.
The normalized window is

\[
(0,1,3,7,6,14,10),
\]

where the integers denote binary cube vertices. The counted centres become
3 and 6. Each count is the number of unselected opposite corners among its
21 allowed squares. Their concatenated lists have 42 occurrences over 37
distinct vertices. The vertices 18,34,66,130 and258 occur in both lists;
their two occurrences must be retained.

Assume the pair sum is at most nine and neither endpoint has distance two
from both centres. Give each vertex its actual path-membership value and
actual endpoint value. Give each counter register the truth value of its
corresponding prefix-count threshold. The selected clauses are then satisfied:

| Requirement | Selected clauses |
|---|---:|
| The seven displayed window vertices belong to the snake | 7 |
| A selected vertex has at most two selected neighbours | 192 |
| A selected degree-one vertex is an endpoint | 32 |
| Ten specified six-vertex cycles cannot be wholly selected | 10 |
| The 42 corner occurrences have sum at most nine | 435 |
| Seven specified vertices are not endpoints | 7 |

The last seven vertices are 0,10,18,34,66,130 and258. Each is at distance two
from both 3 and 6, so the assumed absence of such an endpoint supplies these
clauses. The complete certificate derives a contradiction from the 683
selected clauses. Its 13,299 deductions and 554,859 propagation hints were
independently replayed, exported with an explicit variable bijection, and
checked by Lean in 51 modules. Separate Lean proofs verify the actual-snake
meaning of the clauses and transfer both distances back through the coordinate
map. The corollary follows because the pair sum is an integer.

The original search included two positive endpoint-parity clauses. Neither
occurs in the trimmed proof. The global endpoint-count counter is also unused.
These omissions are checked against the original clause identities, and the
final theorem contains no parity or external contradiction assumption.

The other seven vertices in the common distance-two sphere are
5,15,23,39,71,135 and263. Each is adjacent to the selected internal vertex 7.
Its two path neighbours 3 and 6 already exhaust its allowed selected neighbours,
so none of those seven vertices can be selected. This explains the smaller
set used by the certificate without changing the stated geometric conclusion.

The semantic compilation required two repairs. Both failed attempts, their
sources and logs are preserved. The corrected compilation and final
assembly passed. All final theorem reports use only propext, Classical.choice
and Quot.sound. No missing proof or native-decision axiom occurs in the final
statements. This is a computer-assisted proof of the displayed local theorem;
no claim of historical novelty is made.

## Why a uniform credit remains insufficient

In the fixed first-profile graph from milestone 131, the four-edge cycle has
mean 488 and two qualifying suffix occurrences. Giving each such occurrence
credit \(C\ge0\) bounds any resulting minimum mean by \(488+C/2\).
The other saved seven-edge cycle has no such occurrence; under the same
first-profile weights its mean is \(3453/7\). Thus

\[
\mu\le488+C/2,\qquad \mu\le3453/7.
\]

For a nonnegative mean \(\mu\) and potential range \(R\), the existing comparison with an
allowance of two occurrences is

\[
\frac{1098960+8\mu+2C+R}{4200+\mu}>235.
\]

Lean checks this conditional arithmetic and its extension to every allowance
at least two. The cycle data and the charging formula remain explicit premises;
this assertion does not turn the finite graph into a global snake bound.
The independent written calculation gives the stronger gap

\[
\frac{1098960+8\mu+2C+R}{4200+\mu}
\ge235+\frac{37}{32853}.
\]

Indeed, the numerator of the difference from 235 equals

\[
(2C-4\mu+1952)+223(3453/7-\mu)+R+37/7\ge37/7,
\]

and \(0<4200+\mu\le32853/7\). The sharper numerical gap is written and
independently reviewed; the current Lean statements check the strict
inequality and the allowance extension.

## What remains open

The endpoint theorem restricts repeated low-pair windows to the geometry near
the actual endpoints. The next useful task is to count their possible
arrangements, including overlap between windows. The earlier bound thirteen
uses the intersection of the distance-two spheres of BOTH endpoints. The new
existence conclusion does not justify applying that bound separately to each
endpoint or asserting an allowance of 26.

Even a new occurrence bound must be checked against the competing seven-edge
cycle and the potential range. The uniform-credit calculation above explains
why endpoint proximity alone does not yet establish an improved upper bound.

The maintained global interval remains 191–235, with the existing independent
rebuild limitation. The value 196 and optimality remain unresolved. Existing
notation is retained; no additional named mathematical quantity is needed.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
readme=update.replace('# Research update: milestone 132','# Milestone 132: a parity-free endpoint consequence',1)
readme+='''## Evidence and continuation

- MATHEMATICAL_NOTE.md gives the theorem, proof structure and numerical limit.
- lean/ActualEndpoint132.lean states the actual-snake conclusions.
- data/ActualEndpoint132-audit.json records the successful combined check.
- data/replay-progress.json records the complete 51-module refutation.
- audit/endpoint-core-review.md and audit/endpoint-export-review.md distinguish
  independent original-clause and export reviews.
- work/certificate contains the native certificate and exact selected clauses.
- data/semantic-preparation.json preserves the initial source preparation;
  data/semantic-repair2.json records the corrected source and initial failures.
- data/independent-credit-audit.json and audit/credit-limitation.md record the
  conditional arithmetic limitation and its cycle premises.
- data/verification.json, checkpoint.json and file-manifest.json fix saved scope.

Keep failed attempts and exact snapshots. Do not restart the completed 132
search, replay or semantic checks. Inspect the separate live 115 job before
any restart. Paper revision 126 remains unchanged, with revision 136 next.
'''
(H/'README.md').write_text(readme,encoding='utf-8',newline='\n')
prompt='''# Continuation after milestone 132

Work in E:/Snake-in-a-box and use the requested research skill. Keep existing
notation, defining only essential repeatedly used quantities. Preserve the
three authors, hyperlink settings, unrelated .gitignore and milestone 50 edits,
all failed attempts, and active verification jobs. Fetch GitHub each round.

Read milestones/132-odd-pair-endpoint/MATHEMATICAL_NOTE.md and the saved audits.
The local theorem is complete: for any actual Q9 snake, a fitting canonical
012032 window and alpha[r+2]+alpha[r+4]<=9 force one endpoint at distance two
from both centres.
Equivalently, absence of such an endpoint forces the pair sum>=10. No parity
assumption, external refutation premise or unproved global table is needed.
All 51 refutation modules, actual clause interpretations and the final
coordinate transfer passed Lean. Both failed semantic attempts are preserved.

Do not rerun the completed search or replay. The proof uses 683 original
clauses, 13,299 deductions and 554,859 hints. The 42 corner occurrences include
five vertices counted twice. Neither positive endpoint-parity clause nor the
endpoint-count counter is used.

NEXT SELECTED TASK: derive a sound restriction on the occurrence and overlap
of pair<=9 windows using the actual endpoints. The earlier bound of thirteen
requires both endpoints and cannot be applied separately to give twenty-six
for this theorem.
Keep this as one endpoint-geometry route; avoid unsupported numerical budgets.

Do not expect a uniform credit alone to prove 234 in the fixed first profile.
The surviving four-edge cycle gives mu<=488+C/2; the seven-edge cycle gives
mu<=3453/7. For nonnegative C, mu and R and an allowance at least two, the
existing comparison stays above 235. Lean checks this conditional arithmetic.
The independent written gap is at least 37/32853 above 235. Additional
geometric exclusions or constraints on the competing cycle are required.

The milestone 131 finite comparisons remain 235 and 234 under inherited
unproved hypotheses. The maintained global interval 191–235 has an incomplete
independent rebuild of the contributor upper proof. The optimum and 196 remain
open. Paper revision 126 is unchanged; the next full revision is 136. The
separate milestone 115 job remains resumable; inspect its process, lock and
latest checkpoint observation before taking action.
'''
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8',newline='\n')
print('Wrote theorem, limitations, current records and continuation.')
