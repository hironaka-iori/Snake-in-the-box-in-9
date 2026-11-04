# Retaining the corner-share loss

This note concerns a conditional arithmetic refinement. Lean acceptance is
recorded separately in `data/remainder-completion.json` when present. It
does not establish a new unconditional snake bound or a positive lower
bound for the corner-share loss.

The manuscript already defines the integer shares and the remainders
\(r_{12}(q)\), including unassigned empty corners with no selected neighbour.
Its exact identities give

\[
G_{12}+840(m+1)+\sum_q r_{12}(q)=221136.
\]

Combining this with the existing window inequality and potential premise,

\[
W+2520\le5G_{12},\qquad
\mu(m-8)\le W+R+24C,
\]

gives the sharper conditional comparison

\[
(4200+\mu)m
\le1098960+8\mu+24C+R-5\sum_q r_{12}(q).
\]

No new mathematical definition is needed. The earlier comparison follows
by discarding the final nonnegative term.

## Exact threshold at the two saved witness constraints

The weaker-floor calculation in milestone158 supplied the constraints
\(9\mu\le4462\) and \(R\ge9\mu-3861\). Their equalities hold at
\(\mu=4462/9\) and \(R=601\). With \(C=0\), the comparison gives:

| Assumed total loss | Comparison value |
| --- | --- |
| \(\sum_q r_{12}(q)=3\) | \(235+40/42262\) |
| \(\sum_q r_{12}(q)=4\) | \(235-5/42262\) |

Thus an integer loss of at least4 is exactly the threshold below235 at
these fixed parameters. The two saved witness constraints alone would then
be consistent with the desired strict comparison. This does not construct
a potential for the full retained graph.

More precisely, if the displayed window and potential premises hold for
an actual snake at these parameters, and its total loss is at least4,
integrality gives an edge length at most234. The new arithmetic check
keeps all these hypotheses explicit.

To obtain a numerical snake bound from this possibility, the full potential,
the actual-snake interpretation and the positive loss bound still have to
be proved. None is supplied by the two saved witnesses. The ongoing
universal012034 share-18 replay remains the primary proof task.

## Aggregation must precede rounding

The residue at a corner is taken after its empty-square counts have been
combined. At degree5 it is \(2e(q)\bmod5\), which need not equal
\(2e(q)\). For example,

\[
72\bmod5=2,\qquad6(12\bmod5)=12.
\]

The accompanying source audit gives a directly checked small induced path
with degree5 and six incident empty squares at the relevant corner.
Consequently, charging a separate remainder to each face would overstate
the loss. The exact scale, edge-count convention and this counterexample
are documented in `review/local-lemma-explanation.md`.
