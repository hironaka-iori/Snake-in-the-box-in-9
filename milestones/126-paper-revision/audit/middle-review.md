# Review of manuscript lines 1101–1861

The complete assigned segment was read in six consecutive ranges:
1101–1230, 1231–1360, 1361–1490, 1491–1620, 1621–1750 and 1751–1861.
The source at review time was `paper/snake9_research.tex`, SHA-256
`5e62b785321b8b624338e484560f3ac16d048699c841deeccc69573fd13be72f`.
All line references below refer to those bytes. Only this review file was
written. No manuscript, author field, hyperlink setting, solver or compiler
was changed or run.

The review found outdated proof-status counts and presentation ambiguities.
It found no algebraic or indexing error in the displayed budget and potential
proofs in this segment. The established statements should be retained.

## Required status corrections

### Lines 1401, 1581–1583 and 1612–1614

These passages still state that twelve of the 1378 reference entries are
checked and 1366 remain. Milestone120 raised the checked total to fifteen;
milestone121 raised it to twenty and proves the exact remaining count 1358.
The full reference-union premise remains unresolved. Its total size, the
2678 oriented pairs, the 1287/732 catalogue sizes and intersection 641 are
unchanged by discharging particular entries.

At lines 1581–1583, replace the progress sentences by:

> Twenty of the 1378 local systems in this union have checked refutations.
> The remaining assumption concerns 1358 systems. The union and its
> indexing are unchanged.

At lines 1612–1614, replace the final recovery statement by:

> Subsequent local inequalities discharge twenty entries. Their checked
> implications identify the full reference premise with refutation of the
> remaining 1358 systems.

Update the corresponding part of line 1401 to the same counts. Add the
appropriate archive citation for milestone121; the earlier recovery archive
alone documents twelve. Source evidence is the checked
`twenty_reference_entries_refuted`, `reference_union_iff_remaining_twenty`
and `remaining_twenty_key_count` statements in milestone121. These source
identifiers are audit references and should not appear in the manuscript.

### Lines 1133–1150 and 1753–1773

Keep the five unfinished count-independent share targets as unfinished:
$012032,012034,012301,012340,012345$. Their respective current conditional
floors remain $16,18,16,16,16$. The milestone121 pair-count theorem and
milestone124 six-count theorem concern singleton counts, not the five-centre
share sum $H$. They do not close these share targets.

Keep the proved floor 12 for $012345$ distinct from its unproved target 16.
The original table's target 20 for $012034$ is historical; the conditional
model uses the weakened target 18. If only one main-text table is desired,
retain lines 1755–1768 and reduce the earlier table to a cross-reference.

Suggested replacement for lines 1133–1150, if the later table is retained:

> The five remaining share bounds used in the conditional comparison are
> listed in Section~\ref{sec:actual-weights}. For $012034$, the required
> floor is 18, reduced from the original target 20. Each unfinished bound
> has a checked Boolean refutation, while its complete proof-assistant
> derivation for arbitrary snakes remains unresolved. The proved floor 12
> for $012345$ is used in the comparison based on established share bounds;
> its stronger floor 16 remains an additional assumption.

The claim about checked Boolean refutations is retained from the existing
archive account. Do not replace it with a claim that the local theorems are
fully proved.

## Separate the baseline graph from later refinements

### Lines 1391–1401, 1413, 1708–1713 and 1851–1860

The graph with 1601856 states, 4947008 accepted keys, 791 compatible contexts
and 127 acceptance classes is the baseline whose interpretation is developed
here. Later milestones refine that graph using additional restrictions and
weights. In particular, the experiments in milestones117–124 retain unproved
count-sum hypotheses, although some later local restrictions are proved.
The phrase “the present model uses recorded proofs for its local rules” is
safe only when explicitly limited to this baseline and its stated reference
premise. It should not appear to certify every rule in the latest experiments.

Recommended section title:

> A finite comparison graph and its interpretation

Recommended replacement for line 1392:

> This section specifies the baseline finite graph, proves how a snake
> determines its state sequence, and accounts for its edge weights.
> The reference-catalogue premise and the full potential certificate are
> stated explicitly. Later refinements are compared separately, with each
> additional local hypothesis retained.

Recommended opening of line 1401:

> The baseline exclusion family contains 1378 keys. Its other filters use
> forty checked short-count restrictions, ten checked interval exclusions
> and three checked history exclusions. The share weights use the proved
> local bounds described below. Twenty reference entries are discharged,
> leaving 1358 local refutations outstanding.

The rest of that paragraph can state that actual-window coverage, placement
of the baseline rules, and the weight budget are checked under the displayed
premises. Keep the unresolved complete potential certificate separate.

The mathematical corollary at lines 1817–1848 remains correct: the stated
potentials give the displayed conditional integer conclusions. Its constants
$(483,551)$ and $(496,602)$ belong to these baseline statements. Do not replace
483 by $2915/6$ inside the existing denominator-one statement. The later
refinement uses a rational mean and additional local hypotheses.

At lines 1851–1860, prefer a fixed evidence statement to “is still being
assembled.” Suggested replacement:

> Exact integer enumeration checks both potential inequalities on every
> accepted key of the baseline graph and agrees with the saved edge set.
> The complete proof-assistant certificate over all 791 compatible
> contexts remains unresolved at the stated verification cutoff. The
> coverage and weight theorems therefore retain the reference-refutation
> and full-potential premises.

Do not insert live batch counts here. Such counts become stale and do not
alter the mathematical premise until the entire certificate is assembled.

## Indexing and statement clarity

### Lines 1121–1127: local count indices

The surrounding paper uses $\alpha_i$ for the count at the global path vertex
$x_i$. This theorem switches to $\alpha_1,\ldots,\alpha_5$ without explicitly
declaring a local reindexing. It can be read correctly from context, but the
following statement removes the ambiguity:

> Suppose $r+6\le m$ and the six transitions beginning at $x_r$ use
> distinct directions. If
> \[
> (\alpha_{r+1},\alpha_{r+2},\alpha_{r+3},\alpha_{r+4})=(4,5,4,2),
> \qquad 6\le\alpha_{r+5}\le21,
> \]
> then $\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge120$.

This preserves the theorem and avoids a new local count definition.

### Line 1344: boundary proposition title

“Twenty-one omitted singleton counts” can suggest twenty-one omitted path
positions. The omitted positions are $0,1,\ldots,7,m$, which are nine distinct
positions when $m\ge8$. Their total contribution is at least 21.
Use “Boundary contribution of twenty-one” or “Lower bound for the omitted
counts.” The statement and proof already use the correct indices, including
the empty-window case $m=8$.

### Lines 1255–1271: historical seven-centre model

This subsection is explicitly historical. Its edge count, potential range
and attaining cycle should remain attached to that saved model. Later local
inequalities do not automatically update its edge set. A short opening such
as “The following calculation concerns the earlier saved graph” would make
this scope unambiguous. No numerical replacement is recommended without
changing the full model description and its evidence together.

## Reduce notation that is used only locally

The repeated notation $\alpha_i,b_i,\delta_i,T,s_0,G_{12}$ is useful and
should remain. The share sum $H$ is used across the share theorems and table;
retaining it is reasonable. The history signature is also reused in several
classification and interpretation arguments. The following shorter-lived
symbols add little clarity.

1. Lines 1274–1278 introduce $z_j$ for a single short discussion. Write the
   charged quantity directly as
   $24\delta_j+\sigma_{12}(x_j)$ in its two appearances.
2. Lines 1281–1292 introduce $G=24(B+D)+\Sigma$, although this is precisely
   the existing $G_{12}$. Use $G_{12}$ in the statement and proof. The
   temporary $D=\sum_j\delta_j$ also competes with the earlier window
   demands. Write the excess sum explicitly in this short proposition,
   especially if the new six-block shortfall argument is added nearby.
3. Lines 1457–1472 and 1600–1608 introduce base-six codes to explain numeric
   implementation. These definitions are internally consistent and their
   shift formulas are correct. If the main paper is being shortened, move
   the coding formulas to the verification appendix and state in the main
   text that a state records the five-count tuple, that a transition records
   the six-count tuple, and that source and target are its first and last
   five entries. This preserves the mathematical state transition without
   requiring readers to follow integer decoding.

Suggested replacement for the mixed-budget statement, retaining its content
and avoiding the extra $G$ and $D$ aliases:

> Put $B=\sum_jb_j$ and $\Sigma=\sum_j\sigma_{12}(x_j)$. If
> \[
> Q\le7\sum_j\delta_j,\qquad6C\le\Sigma,\qquad
> R\le7\left(24\sum_j\delta_j+\Sigma\right),
> \]
> then
> \[
> 168B+R\le7G_{12},\qquad
> 336B+24Q+42C+R\le14G_{12}.
> \]

The proof is the existing substitution. Preserve the explanation that the
second inequality uses two copies of the global budget.

## Integration of the new six-count argument

The new direct counting criteria from milestones124–125 should be stated
before, or clearly separated from, the long technical graph interpretation.
They do not require the reference union, the remembered-window automaton,
or a graph potential. This independence is their main expository advantage.

Use the explicit shortfall sum rather than defining another demand symbol:

$$
\sum_{b=0}^{38}\max\left\{0,25-\sum_{j=1}^{6}\alpha_{6b+j}\right\}.
$$

The checked necessary condition for $m\ge235$ is that this sum is at least
$29+2s_0$. Its opposite sufficient condition, an upper bound of $28+2s_0$,
would imply $m\le234$. No such upper bound is proved. The ordinary empty
square count is the existing $s_0$; implementation terminology about its
four anchored occurrences belongs in the verification account, not in the
mathematical statement.

Keep the following distinctions when integrating the latest work:

- A six-count lower bound of 25 is proved for the seven-transition shape
  $0123041$ and its reversal. Universal floors 25 and 26 remain hypotheses.
- The exhaustive direction coverage has 34 canonical seven-transition
  words and 21 reversal classes. One class has the completed six-count proof.
- Nineteen classes have negative native searches, including that one proved
  class. The other eighteen require checked proofs; $0120310$ and $0120324$
  remain unresolved. None of the new timeouts closes those cases.
- On $0120324$, the checked interval reduction under a total at most 22 gives
  $([1,21],[2,21],[1,21],[3,21],[1,21],[1,21])$. It proves neither floor 23
  nor floor 25.
- The shared four/five-count budget at lines 1208–1239 and the new disjoint
  six-block argument are separate valid accounting tools. Combining their
  contributions would need a new common-capacity argument; do not add their
  improvements without checking overlap.

The new results should be presented as mathematical statements with their
proofs and ordinary archive citations. Lean source names, process status,
module totals and failed-run details are useful audit evidence, and can stay
in the research archive or a concise verification appendix.

## Preserved mathematical checks

The following claims in the reviewed segment were checked for arithmetic,
index placement and logical premises and need no mathematical correction:

- The factor-seven excess capacity and both mixed-charge inequalities.
- The shared five-position capacity $4a+c\le120$, including the maximum rule.
- The general $n$-transition boundary constants and telescoping formula.
- The nine-transition boundary contribution 21, including $m=8$.
- The criterion $227p>111960d+R$ for excluding 235.
- The longest-listed-suffix lemma under closure by deleting the last symbol.
- The source/target count shifts, reversal positions and internal interval
  equivalence with truncated symbol six.
- The 81-case completion argument for each eleven-direction signature,
  and the requirement to prove every compatible word's share bound.
- The need to retain the full edge key when endpoint pairs coincide.
- Both actual total-weight estimates and the conditional substitutions
  $4683m\le1103375$ and $4696m\le1103530$.

These are bounded manuscript checks, not a fresh reconstruction of every
computational proof dependency. Authors and local hyperlink settings require
no change from this review.
