# Exact model for four free coordinate histories

This is a written model review. No numerical search, solver, or compiler was run. The proposed pair constraints and merging are exact. The parity statement needs the initial-source-word qualification described below.

## 1. Indexed pair criterion

Write the fixed source path as $P=((z_i,s_i))_{i=0}^{m}$, where $z_i\in Q_4$ contains the fixed base coordinates and $s_i\in Q_4$ contains the chosen block coordinates. A candidate is $Q=((z_i,u_i))_{i=0}^{m}$. Hamming distance decomposes as

$$
d\bigl((z_i,u_i),(z_j,u_j)\bigr)=d(z_i,z_j)+d(u_i,u_j).
$$

Consequently the candidate is an induced path in its specified order exactly when every pair $i<j$ satisfies

$$
\begin{cases}
d(z_i,z_j)+d(u_i,u_j)=1,&j=i+1,\\
d(z_i,z_j)+d(u_i,u_j)\ge2,&j\ge i+2.
\end{cases}
$$

The second inequality excludes both repeated vertices and chords. There is no need for a separate global distinctness hypothesis once this pair criterion holds.

For consecutive indices, the source path guarantees base distance zero or one. Base distance one forces $u_i=u_{i+1}$; base distance zero forces block distance one. For nonconsecutive indices, the exact conditions are:

| Base distance | Required block relation |
|---|---|
| $0$ | $d(u_i,u_j)\ge2$, equivalently distinct and nonadjacent |
| $1$ | $u_i\ne u_j$ |
| at least $2$ | no restriction |

Thus all the proposed relations are necessary and sufficient. No metric relation involving three or more candidate vertices is missing.

## 2. Merging consecutive base edges

Merge indices joined by consecutive source edges in base coordinates. These components are contiguous maximal intervals of indices. Every candidate must have constant block word on each interval, by the consecutive-pair condition. Conversely, assigning one block word to each interval enforces precisely these required equalities.

Let $a(i)$ be the interval containing index $i$, and write $u_i=x_{a(i)}$. Substitute this expression into every indexed pair condition. For each pair of interval variables, intersect all conditions arising from the original index pairs. This preserves every condition, including pairs whose two indices belong to one interval.

Self-pairs must be evaluated, not discarded. A nonconsecutive pair in one interval with equal or neighbouring base words would impose an impossible relation on $d(x_a,x_a)=0$. A valid induced source cannot contain such a pair: its source block word is also constant throughout that interval, and such a pair would repeat a source vertex or give a source chord. Nevertheless, retaining the self-pair consequence is required for a generic correct model. An implementation may evaluate a self-pair as a constant condition before creating a binary constraint. A consecutive block edge cannot lie inside one correctly constructed merged interval.

The resulting model is therefore equivalent to all induced targets with the fixed indexed base words. This argument does not require the interval variables to receive distinct values; different intervals may legitimately reuse a block word when their base positions permit it.

## 3. Translation, parity, and first-transition normalization

Any target can be translated within the block so that $u_0=0$. This preserves the base histories and all Hamming-distance constraints, so it removes no class under global block isometries.

Let $t_i$ count the block-coordinate source edges before index $i$. Consecutive base edges leave the candidate block word unchanged, and consecutive block edges change its parity. Hence after $u_0=0$,

$$
\operatorname{par}(u_i)
=t_i\pmod2
=\operatorname{par}(s_i)\mathbin{\oplus}\operatorname{par}(s_0).
$$

It equals the unmodified source block parity only if $s_0$ is even. In particular, it does so if the saved source starts at the zero vertex. This initial-source condition should be checked or avoided by using the displayed prefix-count formula. If intervals are numbered chronologically from zero, their required block parities are simply the interval numbers modulo two, since each boundary is one block edge.

These parity restrictions follow from the consecutive constraints and $u_0=0$. Adding the correct restrictions only removes redundant domain values. Adding the unshifted source parities when $s_0$ is odd would incorrectly exclude every normalized solution.

Before the first block transition, the candidate remains at block word zero. Immediately after that transition it is a unit word. A global permutation of block coordinates can send that unit word to $0001$. Thus fixing the first block transition to the word represented by integer one is a valid additional normalization. It leaves permutations of the other three block coordinates; it is not a complete quotient by all block isometries.

For the saved $99$-vertex path, a first block transition exists for every four-coordinate partition. Otherwise the whole path would lie in one block slice and could contain at most $2^4=16$ distinct vertices. Therefore this normalization applies to all $\binom84=70$ choices without needing a claim that every individual coordinate occurs as a transition.

## 4. Compact generic Lean statements

The main reusable theorem should be the indexed pair criterion of Section 1, for arbitrary base and block dimensions. Define an indexed induced path by consecutive Hamming distance one and nonconsecutive Hamming distance at least two, or prove this equivalent to the repository's existing snake predicate. The proof uses the Hamming-distance decomposition and the three possibilities for base distance. This avoids dependence on the solver's variable representation.

A second theorem substitutes an interval assignment $x$ through a map $a$ from indices to intervals. Its premises state that adjacent base transitions are merged and that every indexed pair condition is included in the corresponding variable relation. Soundness follows by substitution into the pair theorem. Completeness follows because every target is constant along the merged intervals; choosing the value at one index of each interval defines the required assignment.

For a finite constraint model, define each binary relation as the intersection of the indexed relations it represents. The bridge to a generated table must establish that exact intersection, including self-pairs and every original nonconsecutive index pair. The relation is symmetric in its two block values, but table direction and domain indexing still need their actual interpretation verified.

Separate normalization lemmas show that any target has a block-isometric representative with initial word zero and first block transition $0001$. The parity formula is a further derived lemma. Keeping these separate distinguishes exact representation of normalized targets from coverage of arbitrary targets up to the stated symmetry.

## 5. Scope of the resulting search

All 70 choices are covered by enumerating the four-element subsets of the eight coordinate positions and taking the complement as the block, or vice versa. Every choice has a normalized copy of the original source as a feasible target. An empty feasible set for the unrestricted model would therefore reveal a modelling or implementation error, unless additional exclusions or objectives had been imposed.

The model includes the previously studied slice-isometry family and allows additional slice correspondences. Feasibility alone does not show an escape from the original cube class. A new-class claim requires comparison under the intended full ambient cube-isometry and path-orientation convention. Failure of one slice correspondence to extend to a block isometry can show that a candidate lies outside the slice-isometry family for that particular partition, but it is insufficient to prove a new full cube class.

The candidate length remains $98$ edges. A new embedding could supply a different parent for later constructions; the exact model itself yields no stronger length bound.
