# Joint traversal of the existing potential trees

## Proof

A six-digit base-six code $c<6^6$ determines the existing source offset
$\lfloor c/6\rfloor$ and target offset $c\bmod6^5$. The source therefore uses
the first five digits and the target the last five. While traversing the
acceptance diagram, the checker can select the appropriate potential
subtrees at the same digit positions.

Selection at a potential node is permitted only when the stored interval
width equals the expected width. If a digit is $j<6$ and the residual index
is $u<w$, the existing evaluator at index $jw+u$ equals the evaluator of
the selected child at index $u$. A constant leaf remains constant at any
remaining depth. These statements are checked in Lean.

The induction for joint traversal uses the original code interval. With
$d$ digits unread and prefix $p$, the codes lie in

$$p6^d\le c<(p+1)6^d.$$

For $d\ge1$, after choosing digit $j$, the interval becomes

$$ (6p+j)6^{d-1}\le c<(6p+j+1)6^{d-1}.$$

The quotient and remainder identities identify the same source and target
indices after each selection. The first target digit is skipped; the last
source digit is skipped. Rejected acceptance branches require no potential
check. At an accepted leaf, the checker evaluates exactly the original
capped inequality. Consequently, successful joint traversal implies the
existing prefix check, and the previously proved bounded transfer gives
the original graph-context check.

This is a one-way success implication. A malformed node width may cause
the new checker to fail even when the original evaluator succeeds. The
proof does not rely on any unproved global shape property of the potential
trees. It also preserves the original minima with 551 and 602.

## Checked comparison

Lean checked the general implication from successful joint traversal to
the existing prefix checker. Both source and target digit schedules, the
rejected-branch rule and the potential-width checks are covered. There are
11 checked modules and 26 distinct theorem axiom audits.
Only two reusable implementation definitions were added: branch selection
and joint traversal. No mathematical terminology or manuscript definition was added.

Four matched sequential comparisons passed, including transfer to the
original full context checker:

| Profile | Direction/history | Baseline seconds | Joint seconds |
| --- | --- | ---: | ---: |
| completed | 99/37 | 58.703 | 83.422 |
| completed | 0/0 | 59.734 | 85.609 |
| conditional | 99/37 | 61.734 | 29.969 |
| conditional | 0/0 | 122.250 | 71.766 |

Each pair uses the same imports, weights, potential roots, clipping bound,
acceptance root and candidate codes. No other Lean compiler was active at
launch. These are end-to-end module times from one pair per profile and
context; unrelated system activity was not isolated. They do not establish
a universal performance ordering.

The provisional batch choices, based on total time for the two contexts in
each profile, are completed: baseline; conditional: joint.
The batch should preserve a fallback for a context that exceeds its limit.

These contexts were already certified. Coverage therefore remains six of
791 contexts per profile: 34,701 accepted edges for the completed profile
and 34,148 for the conditional profile. There are 785 contexts per profile
still pending. Comparisons do not add distinct graph coverage.

## Complete batch

A source grouping of the proposed checks gives:

| Profile | Contexts | Distinct expressions | Repeated expressions |
| --- | ---: | ---: | ---: |
| completed | 791 | 591 | 200 |
| conditional | 791 | 578 | 213 |

The grouping requires identical acceptance root, both potential roots and
all inputs to the exact reduced weight expression. This source analysis
does not itself certify reuse. Each reused theorem must still elaborate
and pass Lean against the explicit expression, followed by transfer to
the original direction/history context. Equal acceptance classes alone
are insufficient.

Prepare one resumable sequential batch for all remaining contexts, reusing the six existing certificates per profile. Reuse one verified reduced check per identical acceptance root, weight expression and potential-root pair, then prove each original context by the bounded transfer. Select the baseline or joint method from the measured evidence, with a fallback for timed-out contexts. Assemble the original complete-graph theorem only after every context and every missing block are covered. Do not start another series of isolated timing pilots.

## Remaining mathematical obligations

The maintained project interval is $191\le a(9)\le235$ edges. The upper bound
retains the inspected contributor theorem and archived audit; a complete
independent rebuild is pending. The target 234 remains conditional. The
optimum and conjecture 196 remain unresolved.

The full graph certificates are pending. Both global chains also retain
AllRefuted6K235 and AllRefuted236. The conditional chain additionally needs
the five local refutations with caps $(15,17,15,15,15)$, giving floors
$(16,18,16,16,16)$. The stopped original case7302 target 20 evidence is
unchanged. A target 18 proof requires separate files.

The first traversal proof attempt had three tactic simplification errors.
The corrected source passed. The exact unsuccessful source and log remain
saved. No compiler is active at this checkpoint.

The paper remains revision 96 with all three authors and hyperlink settings
unchanged. The next scheduled full revision is 106.
