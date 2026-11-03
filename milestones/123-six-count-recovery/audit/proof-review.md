# Independent review of the case10 semantics and excess accounting

The five requested modules passed the saved Lean checks. Independent inspection found no mathematical indexing or accounting defect in `SixCharge123.lean` or `GuardedCharge123.lean`. This review establishes the scope and integrity of the semantic and arithmetic results. It establishes neither the case10 contradiction nor a universal six-count lower bound of 26.

The receipt audit verified 177 distinct file hashes and two contextual pins: current sources, corresponding source snapshots, objects, logs, checker snapshots and current checker, every dependency recorded in the five receipts, resolved direct imports, and matching successful run records. All seven printed axiom reports agree with their receipts. Six contain only `propext`, `Classical.choice`, and `Quot.sound`; `maximum_preserves_five_credit` uses no axioms. None of the five selected sources contains `sorry`, `admit`, or `native_decide`.

| Module | Check time, seconds | Printed reports |
|---|---:|---:|
| `Recovered123G.LocalWindowCnf.SixFour10` | 34.594 | 0 |
| `Recovered123G.LocalWindowSat.SixFour10` | 103.547 | 0 |
| `CaseSemantics123` | 1.984 | 1 |
| `SixCharge123` | 53.062 | 4 |
| `GuardedCharge123` | 16.281 | 2 |

The semantic theorem states that the local axioms for direction word $0123042$, with all six internal counts exactly 4, produce a satisfying assignment for the recovered core CNF. `CaseSemantics123` prints that theorem's axioms. The CNF and semantic modules do not prove that this CNF is unsatisfiable. The 202-module case10 export plan has 200 further modules outside this review, and none had a receipt when the review JSON was saved. Its proof data, deduction checks, and final contradiction therefore remain uncompiled in this evidence snapshot.

For the six-window accounting, the positions are $r,r+1,\ldots,r+5$. If $r<N$, the largest possible index is $N+4$, so `range (N+5)` is the correct containing range. For each fixed shift, addition is injective and its image lies in that range. Nonnegativity permits enlargement of the sum; summing the six shifted inequalities gives

$$
\sum_{r=0}^{N-1}\sum_{j=0}^{5}e_{r+j}
\le 6\sum_{k=0}^{N+4}e_k.
$$

The proof also covers $N=0$. Multiplying by $0\le C\le20$ gives the stated total coefficient 120. The aggregate deficit lemma retains $L\le A$, $B\le A$, and $C\ge0$ as premises. It does not supply a geometric lower bound $L$.

The prior five-count contribution occupies $r+1,\ldots,r+5$, the last five positions of the six-count window. In the proposed nine-transition graph placement, the six actual centres are $t+3,\ldots,t+8$; substituting $r=t+3$ leaves the prior five centres $t+4,\ldots,t+8$. This is the correct arithmetic alignment. Actual graph realization and weight assembly are separate obligations. `max_credit_le` combines the two alternatives by their maximum at coefficient 20. Adding both credits, or retaining an unconditional coefficient 24 for the earlier alternative, is not justified by that theorem.

`GuardedCharge123` retains coefficient 24 under the explicit premise $\alpha_r\le6$. Then $\alpha_r-\min(6,\alpha_r)=0$, and the entire six-count deficit is bounded by the excess in the last five positions:

$$
24\max\left(0,L-\sum_{j=0}^{5}\min(6,\alpha_{r+j})\right)
\le24\sum_{j=1}^{5}\left(\alpha_{r+j}-\min(6,\alpha_{r+j})\right).
$$

The Lean statement uses natural-number subtraction for the nonnegative deficit. The coefficient is compatible with the existing five-window overlap budget because $5\cdot24=120$. The companion theorem again permits a maximum of alternative credits bounded by the same budget. The graph symbol 6 represents the interval $[6,21]$, so that symbol alone does not imply the required actual bound $\alpha_r\le6$. A first symbol at most 5 suffices; an actual count equal to 6 requires separate evidence.

The receipts inherit the sentence “Only the actual-snake exclusion and printed statements in this module are checked.” This is stale checker wording and overstates their scope. The checked source statements have the narrower scope described above. The original receipt bytes were preserved, and the discrepancy is recorded in the audit JSON. No actual-snake exclusion, floor26 theorem, completed graph certificate, or improved upper bound follows from these five modules.

Reproduction uses `scripts/audit_receipts.py`; without `--output` it prints a summary, and an output argument creates a new file exclusively. It does not invoke Lean, a solver, proof replay, or graph enumeration. The review checks all dependencies expressly recorded by the receipts and their direct import resolution; it does not rebuild every transitive dependency.

Evidence pins:

- `data/proof-review.json`: `2033778163e5c8406a8bcb17496a43b7177037da90aaae659e917c9ed17cc3f9`.
- `scripts/audit_receipts.py`: `a9ae3443ba281c215a128f9dd6227dd56801a0a801c0c5160e6403713dfc7881`.
- Compilation checker and both saved checker snapshots: `1e12d63df28c0113e37ebb22a1a1d2caaac9bfd61f46044b2f97d19cd228f0db`.
- All five individual source, object, receipt, log, import, and dependency hashes are retained in the review JSON.
