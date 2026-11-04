# Count-conditioned critical-window share theorem

The final saved-evidence audit has passed. For any snake
\(P=(x_0,\ldots,x_m)\) in \(Q_9\), consider a six-transition window
with \(r+6\le m\). Either of the following is sufficient:

1. Its forward canonical directions are 012032 and
   \(\alpha_{r+1}=4,\ \alpha_{r+2}\le4,\ \alpha_{r+3}=4,
   \ \alpha_{r+4}\le5,\ \alpha_{r+5}=3\).
2. Its reversed transition sequence has canonical directions 012032 and
   the counts in the original order satisfy
   \(\alpha_{r+1}=3,\ \alpha_{r+2}\le5,\ \alpha_{r+3}=4,
   \ \alpha_{r+4}\le4,\ \alpha_{r+5}=4\).

Then \(\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge17\).
The count conditions remain; no separate contradiction premise remains.
The universal 012032 floor established in milestone 152 remains 16.

The checked evidence consists of:

- 98 interpretation and coordinate/reversal-transfer modules, with 100
  axiom reports, recorded in milestone 154's semantics-completion.json.
- 137 complete contradiction-replay modules, including the 34 accepted
  pilot modules, with 407 axiom reports. The same 11,869-clause core yields
  the empty clause after 30,305 deductions and 1,754,767 references.
- One final actual-snake composition and its axiom report. The auditor
  checks its exact hypotheses, the forward and reverse count order,
  sources, compiled objects, logs, checker identities and dependencies.
  Only the permitted standard axioms occur in these reports. The external
  Lean and mathematics libraries remain trusted.

The authoritative completion record is data/actual-snake-completion.json.
The existing scripts/audit_actual.py --verify-only command rechecks its
saved evidence without compiling Lean. Earlier pilot and preparation
records retain their original bytes and describe earlier stages.

For the saved retained graph, broadening the count conditions adds no
matching rows: its pair-sum condition already forces the relaxed counts
back to 4 and 5. Applying the proved floor to the two matching eleven-cycle
edges raises its saved total from 5456 to 5458 relative to the universal
012032-floor-16 profile. The fourteen-cycle has no matching edge.
This calculation does not certify a potential on the entire graph.

No new global bound follows from this milestone. In particular, the
conditional 234 comparison still needs local floors (18,16,16,16) for
012034, 012301, 012340 and 012345, their required interpretation and
reversal, reference refutations and a complete potential certificate.
The maintained 191--235 interval retains the paper's distinction between
the contributor upper-bound proof and its pending independent rebuild.
The next useful step on this route is to include the proved local floor
in the graph weights and seek an improved potential, keeping the full
edge verification and boundary accounting as explicit obligations.

The two existing paper sources have been updated in place with identical
bytes. Authors, preamble and local hyperref settings are preserved. The
revision record data/paper-revision.json gives input/output hashes and
backups. This source update performs no TeX compilation and asserts no
new PDF check. The last full paper rewrite remains 146 and the next is 156.


## Subsequent document check

The saved source compiled successfully in the existing desktop editor.
The two paper copies are identical; the preamble, authors and hyperref
settings are unchanged. See data/paper-compile.json and
data/paper-source-review.json. No page-by-page visual review is claimed.
