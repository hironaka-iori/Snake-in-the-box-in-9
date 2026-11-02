# Exact context equations and further potential checks

## Purpose and argument

The weight and endpoint formulas previously repeated fixed table lookups for
every count code. For each direction and stored history, these lookups can be
evaluated once without changing the edge weight.

The proof first filters the existing history-rule catalogue by its suffix
condition. A list induction proves that omitted rules contribute zero and
that the maximum of the remaining contributions equals the original value.
The selected list is checked against the original catalogue in its original
order, including multiplicity. Each retained rule still uses its original
count-cap test, geometric credit and stronger credit.

The direction equations evaluate the geometric credit, both count-free
floors and the five conditioned rules. The latter use the exact forward and
reverse canonical words. Each context then combines these equations with
the checked selected list. Source and target equations preserve the history
update and the original state numbering. The weight and endpoint equalities
hold for all natural count codes, without a hidden range assumption.

Only one reusable evaluator is added to the proof implementation. The
generated files add equations, without introducing further mathematical
definitions or a replacement graph model.

## An emitting history rule

In direction 99/history 37, index the six encoded count symbols from 0 to 5.
The single emitted history rule contributes 19
when $c_1\le2$ and $c_2\le2$, and contributes
18 otherwise. The other conditioned contribution is 96 when the last-five
count code is 3221, and zero otherwise. The geometric contribution is 5;
the completed and conditional floors are respectively 0 and 18.

Consequently, both profile weights agree in this context: the history credit
already supplies at least 18. Lean checks the explicit piecewise formulas and
their equality for every count code. The profiles still use different
potential arrays and slopes, so their potential inequalities require
separate checks.

Exact numerical selection finds 6,043 accepted count codes. Four make the
capped history credit increase the final credit from 18 to 19 in both
profiles. These observations selected a relevant test case. Its full
potential inequalities are subsequently checked in Lean and transferred back
to the original context checker.

## Verification

All 505 direction lookups and all 791 context equations passed Lean. The
context equations preserve the exact selected rule list, source and target,
acceptance class, and both weight profiles. They hold for every natural count
code. The combined import check found no declaration conflict.

The milestone has 30 checked modules and 5,767
distinct theorem axiom audits. The only permitted logical axioms are
`propext`, `Classical.choice` and `Quot.sound`; no incomplete proof or unchecked
native evaluation is used. Exact sources, snapshots, logs and dependencies
are recorded in the proof summary and individual receipts.

The complete finite checks now comprise two contexts per profile:

| Profile | Direction/history | Accepted edges | Compiler seconds | Milestone |
| --- | --- | ---: | ---: | ---: |
| completed | 35/0 | 7,151 | 121.703 | 100 |
| conditional | 177/43 | 6,598 | 165.719 | 100 |
| completed | 99/37 | 6,043 | 111.750 | 101 |
| conditional | 99/37 | 6,043 | 194.312 | 101 |

Direction 99/history 37 is checked under both profiles, so its 6,043 accepted
keys must not be counted twice as distinct graph edges. Coverage is 13,194
accepted edges for the completed profile and 12,641 for the conditional
profile. Each context theorem covers all 46,656 candidate codes through the
checked acceptance traversal. The earlier 207 pilot edges are already included.

The complete graph inequalities still need 789 contexts per profile. The
all-context evaluator equations do not discharge those finite inequalities.
Compiler times are observations from the recorded runs. Some equation batches
overlapped the independent finite-check queue, and memory limits temporarily
delayed new batches. These times are not a controlled performance comparison.

## Consequences and remaining work

The maintained project interval remains $191\le a(9)\le235$ edges. The upper
bound retains the inspected contributor theorem and archived audit; its
complete independent rebuild is pending. The target 234 remains conditional.
This milestone does not claim a smaller bound or settle the conjecture 196.

Both final chains retain the reference catalogues AllRefuted6K235 and
AllRefuted236. The conditional chain additionally retains the five local
refutations with caps $(15,17,15,15,15)$, giving floors $(16,18,16,16,16)$.
Equalities between executable weight formulas do not establish these local
share bounds. The original case7302 target 20 replay remains stopped and
unchanged; a target 18 attempt requires separate evidence.

All context weights and endpoints are now available in reduced form. The
next repeated lookup to examine is the potential itself. For a fixed source
or target state block, the balanced root lookup can potentially be replaced
by its recorded subtree. The proof must preserve the original range cap and
establish the relevant count-code bound. This is a proposed optimization,
with no measured speed improvement claimed here.

In particular, reducing the source potential to one fixed block requires
$c<46656$, hence $c/6<7776$. A source-block equation must not be asserted for
all natural codes. A subsequent transfer can use the existing accepted-code
soundness theorem and the interval checker with this bound kept explicit.

The numerical grouping into 582 joint context classes still needs Lean
equality and transport proofs before certificates can be reused across
groups. Matching acceptance classes or endpoint pairs alone is insufficient.
The existing context proofs should be reused in every subsequent assembly.

Paper revision 96, the three authors and hyperlink settings are unchanged.
The next scheduled full paper revision is 106.
