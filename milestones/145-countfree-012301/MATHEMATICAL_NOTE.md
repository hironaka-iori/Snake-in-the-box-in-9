# Milestone 145: joint share requirements and the 012301 certificate

The main result is a stronger obstruction for the retained graph comparison.
Adding share floors 16 for both 012301 and 012340 still cannot reach a
comparison below235 while the other weights and occurrence event remain
fixed. Combining the saved eleven- and fourteen-cycles gives the exact lower
bound235+95/2348, for every permitted uniform occurrence credit and every
012034 floor. Fourteen arithmetic statements passed Lean with standard axioms.
The native012301 certificate also passed a complete independent replay.
No new upper bound for arbitrary snakes is claimed.

## The joint restriction

Write F and G for the existing-scale share floors of012301 and 012340.
For F>=11 and G>=4, the fourteen-cycle has weights

256,240+F,736,496,360+F,736,360+G,496,480+F,376,736,360+F,496,720+G.

Their sum is6848+4F+2G. The first two consecutive edges total496+F.
Consequently any valid potential mean mu and range R satisfy

7mu <=3424+2F+G, and2mu <=496+F+R.

The comparison(1098960+8mu+BC+R)/(4200+mu)<235 then requires

457F+225G >9848+7BC.

This already rules out F<=19 with G=4: the comparison remains at least
7723775/32866=235+265/32866. With F=16 it requires integer G>=12;
with F=G=16 and B=24 it requires C<19/3. Smaller floors are covered by
monotonic edge-weight upper bounds, without assuming the affine formula
continues below its stated regime.

The eleven-cycle has shapes012032,012314,012031 only. Its base total5399
and four occurrence events impose11mu<=5399+4C. F,G and 012034 do not
change it. Combining this with the two-edge range constraint at B=24 gives
11329-11F<636C. Eliminating C yields the stronger necessary condition

325F+159G >9074.

Thus F=16 requires integer G>=25 if the eleven-cycle remains unchanged.
For F=G=16 the mean cap is496, the range is at least2mu-512, and
24C>=66mu-32394. Hence

(1098960+8mu+24C+R)/(4200+mu)
>= (1066054+76mu)/(4200+mu)
>=551875/2348=235+95/2348.

The last expression decreases for mu>=0. Equality in the listed arithmetic
relaxation occurs at mu=496,C=57/4,R=480. This does not assert existence
of a potential on the full graph. The independently audited saved-cycle
identities and Lean arithmetic are separate evidence from a full-graph proof.

The existing012032 share 16 target adds 57 to the eleven-cycle total. Together
with012301/012340 share 16 it brings both saved cycles to mean496 at zero
occurrence credit. Other graph cycles and proof obligations remain. This is
the reason to pursue the existing three targets together, rather than spend
more graph evaluations retuning only the uniform credit.

## Complete Boolean replay for 012301

The original source is the72 critical-current pysat3-cap15 certificate:
directions[0,1,2,3,0,1], five count intervals[0,21], radius4, resolution12,
endpoint budget2, and cap15. It has11378 variables and92656 clauses.
Sixteen explicit induced-eight-cycle exclusions are present; six occur in
the12977-clause retained core. They must be justified in the actual-snake
interpretation. No count restrictions were silently introduced.

The independent audit reconstructs the full input, original core identities,
cycle exclusions and exact archives. A RUP-only conversion of the unchanged
historical DRAT completed. An independent direct checker then verified all
285541 deductions and31017505 positive propagation references, with all
12977 original core inputs used and a final empty clause. Original clause
identities, all references and source hashes were checked. The direct replay
took30.859 seconds on this machine.

The first conversion timed out while emitting its reference list. Its partial
trace is preserved. A separate90-second compact-core solver experiment also
timed out; its partial trace is not a proof. Completed and partial outputs are
separated in the archive metadata. Exact originals remain locally; the large
files also have verified gzip archives and a restore script. No certificate
was replaced by a smaller unverified trace.

The complete Lean replay, concrete clause semantics, cycle exclusions,
coordinate mapping and reversal are still required for an actual share 16
theorem. A Boolean contradiction alone does not discharge those obligations.

## Checked parts and pending initial-database assembly

The memory experiment concerns the preserved144 share 18 proof. The generic
initial-tree construction has two checked soundness statements. A separate
28-module chunked attempt checked419 reports:104 part-clause equalities,
104 part-build equalities,104 slice equalities,104 part truth transfers and
three generic truth lemmas. Reports use only standard accepted axioms.

The final constructor assembly timed out after181.610 seconds, under a
180-second limit. Maximum sampled private memory was1248415744 bytes,
below the earlier3GiB failure threshold. Its log is empty and it has no
accepted theorem or object. The whole-CNF-to-initial-tree connection remains
unverified. The prepared prefix-composition module has not been checked.
All failed sources, logs and receipts remain frozen.

The next useful diagnostic separates original-CNF-to-chunk truth extraction
from final tree constructor assembly. The timeout does not identify which
part dominates. Do not restart the unchanged monolithic proof or treat the
104 checked components as the completed bridge.

## Evidence and continuation

Read data/direct-replay.json, data/native-review.json,
data/chunked-bridge-completion.json, data/joint-floor-analysis.json and
data/two-cycle-analysis.json. Arithmetic receipts are data/JointFloors145-audit.json
and data/TwoCycles145-audit.json. The independent bounded review is under audit/.

The next round stays on empty-square shares. Complete the initial-database
connection in smaller independently checked pieces, then transport and replay
the verified 012301 proof. Preserve the012340 and 012032 targets as joint
dependencies. Test a precisely specified combined profile before attributing
sufficiency to these saved-cycle gains. The maintained191--235 project interval
and conditional234 profile retain their previously documented proof limits.
The optimum and196 hypothesis remain unresolved; the goal remains active.

Paper145 is a targeted update, with authors, preamble and hypersetup preserved
and no new named definitions. The next full rewrite remains due in146.
Static source checks and PDF compilation are recorded separately.

## Completed count-sum theorem

The separate milestone 115 batch completed all 1,397 modules during this
round. For every fitting canonical direction window 012310 in any snake,

\[
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+3}+\alpha_{r+4}+\alpha_{r+5}\ge19.
\]

The final theorem has no additional count, endpoint-location or parity
hypotheses. Its complete Boolean replay has 287,753 deductions and
16,816,989 references; the actual-snake interpretation also passed Lean.
The completion audit rechecked every successful source, object, log,
source snapshot, checker snapshot and recorded dependency. This is a fresh
verification of saved results, with no compiler rerun. Exact records are
archived in three ordered parts under certificates/; the original archive
and all original records remain locally. This completes one inherited local
premise, while the global bound is unchanged.
