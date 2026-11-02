# Compatibility and count conditions for rejection witnesses

This note describes a decomposition of the existing finite certificate. It
does not assert a new extremal bound. Lengths of snakes are measured in edges.

## 1. The retained-code implication

Write a six-symbol count vector as

\[
x\in\{1,\ldots,6\}^{6}.
\]

The sixth symbol represents the actual-count interval \([6,21]\). A rejection
box is a product of six integer intervals. A witness identifies one of the
existing reference, short, interval or history exclusions, together with its
placement and orientation where applicable. A valid witness for a box proves
that every count vector in that box fails the original numerical retention
predicate in the specified context.

Let \(q\) be a history index, \(d\) a direction index, \(B\) a box and \(u\)
a witness. Denote the original Boolean validity condition by
\(V(q,d,B,u)\). For a shared geometric class, the cover certificate gives

\[
x\in A\quad\text{or}\quad x\in\bigcup_{i=1}^{r}B_i,
\]

where \(A\) is the set accepted by the saved decision diagram. If every
\(V(q,d,B_i,u_i)\) holds, a retained vector cannot lie in any \(B_i\).
Consequently it belongs to \(A\). The witness list must have exactly \(r\)
entries; a shorter list would leave boxes without justification.

The concrete class-1 result checks 640 boxes against six direction-specific
witness assignments, at direction indices

\[
1,\ 3,\ 307,\ 308,\ 310,\ 312.
\]

There are two distinct witness lists. None uses a history exclusion. The
history-transport lemma therefore extends the checked validity at history
zero to every \(q<75\), while the original retention predicate, including
its history guards, remains in the hypothesis. For each listed assignment,
each \(q<75\) and each code \(c<6^6\), retention implies membership in the
original shared decision diagram. This is the checked scope of the pilot.
It does not establish the complete context-to-class assignment.

## 2. Separating compatibility from counts

Define the **compatibility condition** \(C(q,d,u)\) to contain the history and
direction bounds, catalogue membership tests, applicable placement guards,
and the canonical direction-pattern or history-signature comparison.
Define the **count condition** \(D(B,u)\) to contain the six-coordinate box
length test and the singleton, cap, sum, interval-containment or history-cap
tests. The interval coordinate guard remains with its count test. The
catalogues and lookup functions are fixed parameters of both expressions.

The separation identity is

\[
V(q,d,B,u)=C(q,d,u)\land D(B,u).
\]

This is a rearrangement of the existing checker. It retains invalid-index
defaults, reversal, truncated natural subtraction and the decoded direction
index used by history rules. No catalogue or placement guard may be omitted.
Lean checks the identity for arbitrary supplied lookups and indices. The
accompanying proof receipt records its exact source, output and dependencies.

Once this identity is checked, a family of entries can reuse a compatibility
proof whenever its complete compatibility inputs agree, and a count proof
whenever its complete tested count inputs agree. This does not by itself
justify every proposed compressed descriptor. Each descriptor still needs
an equality connecting it to the source expression.

## 3. A reusable direction-pattern test

For a direction word \(\delta\), offset \(s\), slice length \(\ell\), reversal
flag \(\varepsilon\), and canonical pattern \(\pi\), define

\[
S(\delta,s,\ell,\varepsilon,\pi)
\iff
\operatorname{can}\!\left(
  \operatorname{rev}_{\varepsilon}
  \bigl(\operatorname{take}_{\ell}(\operatorname{drop}_{s}\delta)\bigr)
\right)=\pi.
\]

Here \(\operatorname{rev}_{0}\) is the identity and
\(\operatorname{rev}_{1}\) reverses the list. Canonicalization labels
coordinates in order of first appearance, as in the original checker.

A reference key consists of a pattern \(\pi\) and a count-symbol list
\(\sigma\). Its shape test, placed at count offset \(a\), is

\[
S(\delta,a+2,|\sigma|+1,\varepsilon,\pi).
\]

Thus keys with the same pattern and the same symbol-list length share the
shape test at the same placement and orientation. Their count-symbol values
remain separate singleton constraints. Their catalogue indices and fitting
placement guards also remain separately checked. Sharing the full
compatibility expression by catalogue index would retain much of the
repetition; the shape expression must be isolated explicitly.

## 4. Finite reduction and its limits

The saved materialization has 791 contexts and 543,827 witness occurrences.
Only three occurrences use a history witness, all in position zero. Keeping
the direction fixed, transporting history-free lists and sharing the two
identical tails leaves 507 base validity jobs and three history-head checks.
These contain 357,820 base entries and three heads, saving 186,004 repeated
entry checks relative to the materialization. There are 210 base lists.

The exact computational profile gives:

| Family | Planned entries | Distinct normalized shape tests | Distinct count tests |
| --- | ---: | ---: | ---: |
| Reference | 338,697 | 12,560 | 2,319 |
| Short | 16,341 | 2,260 | 282 |
| Interval | 2,782 | 530 | 48 |
| History | 3 | 3 | 2 |
| Total | 357,823 | 15,353 | 2,651 |

There are also 508 distinct outer-guard descriptors and 2,329 catalogue-guard
descriptors. The profile preserves the original entry positions and the four
descriptor IDs used by every entry. Direct and decomposed evaluations agree
on all planned entries. Every saved entry is true, so that experiment alone
does not establish an identity on arbitrary invalid inputs. The general Lean
identity and the future concrete descriptor correspondences have distinct roles.

The class-1 proof module passed in 21.125 seconds, excluding its data modules
and shared table checks. No comparison with a factored concrete certificate
has yet been measured. The next bounded experiment should check the same six
jobs with normalized reference-shape reuse, including the correspondence and
assembly costs. The simpler checked pilot remains the baseline.

## 5. Consequence for the upper-bound programme

The remaining finite coverage must still be connected to the saved full
edge keys and endpoint columns. Reference-catalogue refutation premises,
pending local shares, interpretation of credits and the full potential check
also remain explicit obligations. This decomposition aims to make those
finite proof checks practical; it does not increase a local share or lower
the numerical bound by itself.

The maintained project interval remains

\[
191\le a(9)\le235.
\]

The upper bound uses the inspected contributor theorem and saved audit; a
complete independent rebuild remains pending. The proposed bound 234 remains
conditional on the outstanding proof obligations.
