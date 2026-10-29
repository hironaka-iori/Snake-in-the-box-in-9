# Milestone 68: remove numerical-only share premises

**Completed research round.** All 24 inherited oriented share rules marked numerical-only can be removed while retaining a conditional upper bound of **234 edges**. The new exact mean is 14392/29 and the potential range is 18984 at denominator 29. The model still uses numerical count exclusions, so the maintained global interval remains **191 ≤ a(9) ≤ 235**.

## Share ablation

Milestone 67 inherited 32 oriented count-dependent share rules from milestones 51–57. Eight are four Lean-checked rules and their reversals; 24 were numerical-only. The new model retains only the eight checked rules, the unconditional nine-direction geometry from milestone 59, and the checked eleven-direction improvements and count restrictions integrated in milestones 65–67.

The new base share is reconstructed directly from these retained rules. It is never obtained by subtracting a guessed contribution from the old maximum. The full transition weight is then reconstructed by taking the maximum of all applicable retained credits on the same centres.

Removing the 24 rules lowers 5,341 source-transition credits and 8,068 complete-model weights. It invalidates 2,605 inequalities of the old potential. A new potential is therefore necessary.

The topology remains exactly the milestone-67 graph: 1,601,856 states and 18,194,151 transitions. Its new exact minimum is

\[
\mu=\frac{14392}{29},\qquad \frac{\mu}{120}=\frac{1799}{435}.
\]

An independently checked potential has range 18984, and a 29-edge cycle attains this mean. Every transition weight and every potential inequality were independently reconstructed and checked. The mean decreases by only 18/145 from milestone 67.

## Conditional bound

The improved boundary budget from milestone 67 remains

\[
W+4200m\le1098960.
\]

If the snake is represented by the new graph, its potential inequality is

\[
14392(m-8)\le29W+18984.
\]

Combining them gives

\[
136192m\le32003960,
\qquad
m\le\frac{4000495}{17024}<235.
\]

Thus the conditional integer bound remains 234. At m=235 the left side of the integer inequality exceeds its right side by 1160. The older boundary budget would allow 235. Seven Lean theorem audits check these deductions, including a natural-number version directly using the charge budget.

This removes all 24 numerical-only share inequalities from the required proof chain. It does not remove the remaining numerical count exclusions, and it does not supply the complete graph-to-snake interpretation.

## Count-dependency inventory

The inherited count catalogue has 28,623 canonical keys. Its pinned contributor-certified reference contains 1,287 keys; 27,336 entries lie outside that reference. This set difference measures catalogue entries, not logically independent mathematical statements.

A contiguous-subwindow subsumption pass retains the reference keys and processes additional keys in increasing window length. If a key contains a retained forbidden subwindow, it receives an explicit shorter premise. This removes 2,057 entries from the additional proof list, leaving:

| Internal counted positions | Additional retained keys |
|---|---:|
| 4 | 17 |
| 5 | 1,610 |
| 6 | 23,652 |
| Total | 25,279 |

Every original catalogue key is independently checked to contain a retained key or to be retained itself. The compressed certificate lists every retained key and every reduction. This verifies catalogue coverage; it does not prove that an unproved key is impossible in a snake.

The next priority is to restore transitions excluded only by the additional keys and determine which restorations violate a sufficient potential bound. This can identify the exclusions relevant to 234 before undertaking a large proof replay. A numerical candidate or a failed potential inequality alone will not be treated as a snake theorem.

## Evidence

- `data/verification.json`: all 18,194,151 reconstructed weights and potential inequalities, with a matching attaining cycle.
- `data/lean-audit.json`: one new Lean module and seven standard-axiom theorem audits for the conditional arithmetic.
- `data/import-audit.json`: prior share proof receipts and selected theorem logs rechecked; 288 recorded source hashes match current sources. These imported proofs were not rebuilt this round.
- `data/dependency-inventory.json`: source hashes and the count/share dependency totals.
- `data/count-subsumption-summary.json` and `data/count-subsumption.json.gz`: exact catalogue reduction and its explicit witnesses.
- `data/share-ablation.json`: removed rules and the effect on the previous potential.

The new graph and potential are checked by executable integer computations. A complete Lean graph certificate, arbitrary-snake normalization/history recognition and the required count proofs remain outstanding.

## Reproduction and manuscript

Run `inventory.py`, `subsumption.py`, `ablate_shares.py`, `analyze.py`, `audit_imports.py`, and `verify.py`. Run `replay.py` followed by `audit_lean.py` for the seven new Lean deductions. Preceding milestone data/builds and the documented local dependencies are required. Generated graph arrays and compiled Lean files are ignored.

This is round 2 of 10 after manuscript revision 66. The paper and editor mirror remain unchanged; the next full revision is scheduled for milestone 76.
