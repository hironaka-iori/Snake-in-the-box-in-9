# Three transition patterns exclude singleton count one

Let a segment of a snake start at vertex index $r$. Assume that $a,b,c,d,e$ are five distinct coordinates. This round proves the following restrictions, with no assumptions on the other singleton counts or on endpoint distances:

| Successive transitions | Counted vertex | Conclusion |
|---|---|---|
| `(a,b,c,d,a,e)` | offset 4 | Singleton count at least 2 |
| `(a,b,c,d,a,e,b)` | offset 1 | Singleton count at least 2 |
| `(a,b,c,d,a,c,e,d)` | offset 7 | Singleton count at least 2 |

All three exclusions, their interpretation for arbitrary snakes, coordinate normalization, and lower-bound deductions pass Lean. Twelve dependency audits use only propositional extensionality, classical choice, and quotient soundness. Sharpness of two for complete snakes is not asserted.

## Why the first restriction holds

Write the first pattern as six transitions beginning at $x_r$, and put $x=x_{r+4}$. Its two path directions are $d$ and $a$. The opposite corner $x+e_b+e_c$ equals $x_{r+1}+e_d$, which is unselected because $x_{r+1}$ already has its two segment neighbors. Hence the coordinate pair $\{b,c\}$ gives a singleton square at $x$.

If the singleton count at $x$ were one, this would be its unique missing pair. The continuation lemma in the paper then requires any second step along either neighboring arm to use $b$ or $c$. The continuation from $x$ through $x_{r+5}$ to $x_{r+6}$ uses $e$, a distinct coordinate, giving a contradiction. This explanation uses the previously proved continuation lemma; the new finite proof checks the exclusion independently from the ordinary path clauses.

## Proof data and controls

| Case | Input clauses | Active variables | Derived clauses | Antecedent references |
|---|---:|---:|---:|---:|
| First pattern | 282 | 276 | 280 | 780 |
| Second pattern | 456 | 455 | 480 | 1295 |
| Third pattern | 829 | 807 | 691 | 3225 |

The models use radius-four neighborhoods, the prescribed segment, selected degree restrictions, the two-endpoint condition, ordinary square and six-cycle exclusions, and the one capped singleton count. No additional cycle cuts are needed. All retained clauses are reconstructed from their original encoding, and every contradiction is replayed in Lean.

Independent geometry checks cover 14 positive local forests and all 131 published bank paths. The first pattern has 6654 oriented occurrences in the bank, with minimum count four; the second has 14, with minimum eight; the third has none. These observations do not establish larger universal constants. Shorter positive local configurations show limits of the tested local exclusions; they do not establish complete-snake sharpness or globally minimal transition hypotheses.

## Effect on the aggregate model

Applying all three rules to every represented subsegment in both orientations removes 57,837 previously retained transitions. The remaining graph has 4,493,893 edges on the same 1,586,304 states. A replacement eleven-cycle attains normalized mean 42/11. An integer potential, checked on every retained edge, proves the matching lower bound; its range is 8064.

The replacement cycle contains no count-one symbol. Consequently, further restrictions that only exclude count-one windows cannot eliminate this cycle or raise this model's minimum. The next research target is joint constraints on its counts of two and three, particularly excess hidden by the symbol for counts at least six. The finite-model result provides no new global snake bound, and its complete arbitrary-snake Lean graph bridge remains pending. The integrated interval remains 191 <= a(9) <= 236.

## Reproduction and manuscript status

`scripts/archive.py --unpack` restores the lossless proof archives. `scripts/certify.py` generates the three ordinary cores and replay sources. `scripts/wrappers.py` states the arbitrary-coordinate results. `scripts/replay.py` builds them in a fresh directory; `--resume` reuses only successfully built, source-matching dependencies. Runtime and support paths are explicit in the scripts.

`scripts/controls.py` independently checks local geometry and the bank. `scripts/graph.py` applies the restrictions and computes the candidate cycle and potential. `scripts/verify.py` checks proof provenance, source/build agreement, axiom receipts, and the exact graph certificate without rerunning the optimizer.

This is research round 1 of 5 after manuscript revision 46. The paper and its editor mirror are unchanged; the next scheduled manuscript revision follows five research rounds.
