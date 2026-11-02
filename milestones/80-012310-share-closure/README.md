# Milestone 80: the 012310 share theorem

The count-free share bound for the canonical six-transition pattern 012310 is
now Lean-checked, including coordinate normalization and reversal. Case7305
passes all 465 generated modules and 100 printed theorem audits. The combined
catalogue passes 35 audits and retains five local share premises, reduced from
six. The maintained global interval remains 191 through 235 edges.

## Mathematical statement

Let p be an induced path in Q9, with a six-transition window whose directions
are a,b,c,d,b,a, where a,b,c,d are distinct coordinates. For a selected vertex x,
define its scale-12 empty-square share by

\[
\sigma_{12}(x)=\sum_{q\sim x}
\left\lfloor\frac{12e_0(q)}{d_S(q)}\right\rfloor,
\]

where e0(q) counts empty square faces through q and dS(q) counts its selected
neighbours. The denominator is positive because x is selected. If the window
starts at index r, then

\[
\sum_{i=1}^{5}\sigma_{12}(p_{r+i})\ge12.
\]

The statement also holds for the reversed pattern a,b,d,c,b,a. It requires no
extra singleton-count hypothesis. The proof uses the universal ceiling 21
at internal vertices when applying the local certificate.

## What was checked

The earlier 86 clause-semantic batches and composition were reused after
matching their sources. The selected refutation replay has now completed,
followed by the refutation assembly, arbitrary-snake geometry and reversal.
The final audit matches the original local encoding, selected CNF clauses and
variable renaming, generated clause data, source hashes and all printed axioms.
Only propext, Classical.choice and Quot.sound occur in those audits.

The full case audit and archives are in
`../73-countfree-share-catalogue/cases/case7305/`. Archive restoration verified
all 465 sources and the compact CNF/LRAT bytes. The older partial archives remain
as historical provenance. Shared imported support is reused; this milestone
does not claim a clean rebuild of the entire inherited dependency closure.

`../73-countfree-share-catalogue/lean/CombinedCatalogue.lean` now contains the
canonical7305 wrapper. Its combined theorem retains exactly cases 7301, 7302,
7303, 7307 and 7308 as local refutation premises. Cases 7300, 7304, 7305 and 7306
are supplied by checked certificates.

## Effect on the comparison graph

The recomputed model verifies every potential inequality on its 4,947,008
edges and an attaining cycle. Its minimum mean increases from 480 to 483;
its potential range changes from 536 to 551. The weight and potential hashes
equal the earlier comparison that assumed the 012310 share lemma. That local
share assumption is now discharged.

Using the current boundary budget, the comparison gives

\[
483(m-8)\le W+551,\qquad W+4200m\le1098960,
\]

and hence

\[
m\le\frac{157625}{669}\approx235.613,
\]

with integer bound 235. This remains a graph-to-snake conditional calculation:
the complete retained-edge, credit and Lean potential assembly is unfinished.
It supplies no new global numerical upper bound. The full mixed target still
has conditional integer bound 234.

## Continuation

Milestone79 already connects exact encoded count tests to actual snake counts
and instantiates the ten completed interval exclusions. Continue that retained-edge
assembly through the reference union, recovered short rules, history exclusions
and exact array lookup. In the same empty-square route, complete the five
remaining count-free share targets. Alternative credits on the same centres
combine by maximum. Exact optimality and the conjecture 196 remain unresolved.

The paper remains revision76; the next scheduled complete revision is round86.
Both manuscript copies, all three author names and hyperlink settings are preserved.
