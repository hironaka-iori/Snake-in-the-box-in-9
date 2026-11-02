# Potential lookup reduction with an explicit code bound

## Argument

The two existing potentials each use 206 blocks of 7776 entries. Once the
source or target block is fixed, its root lookup can be evaluated once.
For natural numbers $b$ and $r$ with $r<7776$,

$$
\left\lfloor\frac{7776b+r}{7776}\right\rfloor=b,
\qquad (7776b+r)\bmod7776=r.
$$

Substitution into the existing potential formula gives its exact value from
the recorded root for block $b$ and offset $r$. The original minimum with
551 or 602 is retained. The 206 root selections for each profile are checked
against the original balanced lookup by Lean; the source-text extraction
used to propose the roots is not trusted as proof.

For an edge code $c<46656$, the source offset is
$\lfloor c/6\rfloor<7776$. The target offset is $c\bmod7776<7776$.
The source reduction therefore needs the explicit code bound. It is not
asserted for arbitrary natural codes. The weight and endpoint equalities
from milestone 101 can still be used without a code bound.

The bounded transfer theorem proves the original context checker from a
successful reduced prefix test. For each code in its interval, a rejected
code satisfies the original edge check directly. An accepted code receives
the reduced inequality from the previously proved prefix soundness theorem;
the bounded equality then gives the original inequality. Direction, history,
count encoding, edge weight and potential cap remain exactly the same.

This is an equality-based reduction in certificate evaluation. It strengthens
neither the local share estimates nor the graph's potential slope.

## Checked results

All 412 fixed-block equations passed Lean, together with the generic
bounded transfer to the original context checker. No definition was added.
The milestone contains 20 checked modules and 441
distinct theorem axiom audits. Successful sources contain no incomplete proof
or unchecked native evaluation; the permitted logical axioms are propext,
Classical.choice and Quot.sound.

Eight new complete profile/context checks passed:

| Profile | Direction/history | Accepted edges | Compiler seconds |
| --- | --- | ---: | ---: |
| completed | 0/0 | 6,123 | 90.516 |
| conditional | 0/0 | 6,123 | 94.672 |
| completed | 1/0 | 6,997 | 85.984 |
| conditional | 1/0 | 6,997 | 119.219 |
| completed | 9/0 | 3,913 | 88.953 |
| conditional | 9/0 | 3,913 | 39.375 |
| completed | 10/0 | 4,474 | 45.250 |
| conditional | 10/0 | 4,474 | 43.531 |

Including the earlier certificates, coverage is:

| Profile | Complete contexts | Accepted edges | Remaining contexts |
| --- | ---: | ---: | ---: |
| completed | 6 | 34,701 | 785 |
| conditional | 6 | 34,148 | 785 |

Each context certificate covers all 46,656 candidate codes through the
checked acceptance test. Counts for different profiles are kept separate.
The repeated comparison context 99/37 adds no coverage.

For that same context, the recorded timings are:

| Profile | Archived implementation, seconds | Fixed-block implementation, seconds |
| --- | ---: | ---: |
| completed | 111.750 | 56.860 |
| conditional | 194.312 | 110.016 |

The archived and current runs had different workloads. These are observed
timings, without a controlled speedup claim or an extrapolation to all contexts.

A separate matched pair changed only the leaf comparison in completed 99/37.
The decidable comparison took 61.672 seconds and direct
Boolean comparison took 92.234 seconds. The runs were sequential,
with no other Lean process at launch. Both prove the same original context
statement. This is one pair; it does not establish performance on other contexts
or isolate unrelated system activity. The semantic equality is checked in Lean.
The direct Boolean variant was slower in this pair and is not adopted as an
optimization. This observation does not prove it is slower in every context.

## Global status and continuation

The maintained project interval remains $191\le a(9)\le235$ edges. The upper
bound retains the inspected contributor theorem and archived audit, with its
complete independent rebuild pending. The target 234 remains conditional.
The optimum and conjecture 196 remain unresolved.

The complete graph certificate still has 785 contexts remaining per profile.
Both global chains also retain AllRefuted6K235 and AllRefuted236. The
conditional chain additionally retains the five local share refutations with
caps $(15,17,15,15,15)$, giving floors $(16,18,16,16,16)$. The original case7302
target 20 record is unchanged and stopped; a target 18 proof requires new files.

The direct Boolean comparison experiment is complete and its limited timing
evidence is recorded above. Both forms use Lean's existing natural-number
comparison; the experiment does not establish a new comparison algorithm.

The next candidate optimization is to reduce repeated descent through the
two potential trees while the acceptance prefix is traversed. Its exact
invariant and shape obligations are discussed in the feasibility note. It has
not yet been implemented, checked in Lean or benchmarked. Successful context
certificates from milestones 100, 101 and 102 should all be reused.

The initial redundant import of an unavailable Omega module failed before
the proof was processed. The corrected source uses the already available
tactic and passed. Both attempts are preserved with their exact source bytes.
No compiler remains active at the saved checkpoint.

Paper revision 96, its three authors and hyperlink settings are unchanged.
The next scheduled full revision is 106.
