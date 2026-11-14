# Slice capacity and square-base saturation

Read the exact interval model and the manuscript's indexed-pair, residual-symmetry, and continuation sections beginning near line 8637. No native search, compiler, or software tests were run. A small read-only audit reconstructed case 23's visit sets and counts from its saved model; it did not rerun the extraction script or solve a model.

## Same-slice capacity

Each chronological interval has one free-word variable. Fix a retained-coordinate word $z$ and a free-word parity $\varepsilon$. Consider distinct interval variables that visit $z$ and have parity $\varepsilon$. Their assigned words must be pairwise distinct: equality would repeat the full vertex $(z,u)$.

Count each interval once, even if a data structure lists several visits. A valid induced source actually cannot revisit $z$ within one interval, since its free word is constant there. A variable can belong to several different slice constraints when its interval visits several base words. Those memberships do not create extra independent variables, and capacities from different slices cannot simply be added.

Let $J$ be any subset of the chosen interval variables and let $D_g$ be their current domains. Every valid assignment injects $J$ into their union of allowed words. Therefore

$$
|J|\le\left|\bigcup_{g\in J}D_g\right|.
$$

A violation rejects the domain region. If equality holds, the variables in $J$ use every word in that union, so those words can be removed from every other variable required to differ from all of $J$.

This can be stronger than binary support propagation. Three pairwise-different variables, each with domain $\{0,3\}$, have support for every value on every binary inequality, but cannot receive three distinct words. Both words have even parity, so the example applies to the same-parity inequality relation. It illustrates the local relaxation, without claiming this exact pattern occurs in a saved model.

Checking only the whole chosen set detects some capacity violations. Proper subsets can give additional violations or tight-set deletions. Satisfying these necessary conditions does not resolve the remaining path constraints.

## Stronger structure when the retained cube is a square

Now there are two retained coordinates and six free coordinates. Write $V_g\subseteq Q_2$ for the nonempty set of base words visited by interval $g$.

For distinct intervals of the same free-word parity, equality of their free words is permitted by their mutual indexed-pair constraints exactly when both visit sets are singleton antipodes.

To prove necessity, suppose the words are equal. For every $a\in V_g$ and $b\in V_h$, their full-vertex distance is the base distance. Distance zero repeats a vertex. Distance one creates a forbidden edge: consecutive base edges belong to the same merged interval, while consecutive block edges have opposite free-word parities. Thus every such base pair must have distance at least two. In $Q_2$, each vertex has exactly one vertex at distance two, its antipode. Since both visit sets are nonempty, every cross pair being antipodal forces both sets to be singletons, at opposite vertices.

For sufficiency concerning these two intervals only, singleton antipodal base words have distance two, so all their cross pairs remain nonadjacent and distinct regardless of equality of free words. This does not assert that an equality extends to a complete target satisfying all other constraints.

For distinct same-parity intervals in every other configuration, the mutual condition is precisely inequality of their words. Indeed, different words of equal parity have free distance at least two, which already makes all their cross pairs nonadjacent and distinct.

Let $M$ count intervals visiting more than one base word, and let $N_z$ count singleton intervals at square vertex $z$. All $M$ variables conflict with every other same-parity variable. Singleton variables conflict within their own class and with both adjacent classes; the only missing conflicts are between opposite classes. Hence a largest clique has size

$$
M+\max(N_0,N_3)+\max(N_1,N_2),
$$

and this quantity cannot exceed the 32 available words of that parity. The bound is obtained by choosing every multi-visit interval and the larger singleton class from each antipodal pair. No clique can contain a member of both opposite singleton classes. This establishes the clique formula without assuming a property of arbitrary graph colouring or of the complete path model.

## Audited saturated case

The saved model for case 23 fixes coordinates $[0,5]$ and has 81 interval variables. Its hash agrees with the extraction record. Independently reconstructed visit sets, multi-visit lists, singleton lists, and chosen cliques agree with that record:

| Free parity | Multi-visit intervals | Singleton counts at $0,1,2,3$ | Clique size |
|---|---:|---|---:|
| Even | 12 | $5,4,10,10$ | 32 |
| Odd | 6 | $9,9,8,8$ | 24 |

The saved 28-case table marks only case 23 as saturated. This review independently reconstructed case 23, rather than all 28 source models.

For the even variables choose the clique consisting of all 12 multi-visit intervals and the ten singleton intervals at each of base words 2 and 3. Its 32 distinct assigned words exhaust the 32 even words. Therefore:

- Every even word is assigned to exactly one variable of this clique.
- Each base-0 singleton must equal the word of one base-3 singleton: it conflicts with every other clique member.
- Each base-1 singleton must equal the word of one base-2 singleton.
- These correspondences are injective within each outside singleton class, because that class itself requires distinct words.

Thus exactly nine even words are shared between two interval variables, each pair lying at singleton antipodes. No word is shared by three intervals. The remaining 23 even words each belong to one interval, although a multi-visit interval uses its word at more than one full-vertex position.

The equalities are existential partner choices. They do not identify a predetermined partner or justify merging every variable with all its possible partners.

## Sound domain consequences of saturation

Let $C$ be the 32-variable even clique, and retain the current sound domains.

1. For every even word $w$, at least one clique domain must contain $w$. Absence of support rejects the region.
2. If exactly one clique domain contains $w$, that variable must be assigned $w$. This uses exhaustion of the entire even-word set, rather than only binary inequality.
3. A base-0 singleton's domain can be intersected with the union of the base-3 singleton domains; a base-1 singleton's domain can be intersected with the union of the base-2 singleton domains. An empty result rejects the region.
4. The capacity inequalities and tight-set deletions apply to every subset of $C$, and to any other set of pairwise-conflicting same-parity variables.

For item 3, take any feasible assignment of an outside variable. Its value occurs at one clique variable by saturation. All clique variables except its antipodal singleton partners conflict with it. The value must therefore occur in one partner's domain. This proves the deletion for every feasible assignment.

These deductions remain valid under domain restriction, branching, and the original global lex inequalities. They are consequences of the same model, so they do not change which full assignments are acceptable. Their computational benefit remains to be measured. A global collection of these inequalities is not an assembled proof of any concrete search exclusion.

## Lean scope

The accompanying `lean/Capacity209.lean` is an uncompiled `Std`-only draft. It gives elementary list proofs that distinct selected values cannot exceed an enclosing finite list's length, that equality forces every enclosing value to occur, and that domain-union capacity follows. It also proves the unique-support and allowed-partner implications under explicit occurrence and conflict premises.

The square geometry, concrete group/parity/visit interpretation, case 23 counts, and the native pruning integration remain separate obligations. No concrete exhaustion is asserted to have been checked by these generic lemmas.
