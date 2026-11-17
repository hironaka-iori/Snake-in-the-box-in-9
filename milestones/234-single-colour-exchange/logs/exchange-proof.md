Compilation update: all four statements passed the guarded Lean compiler. See data/ColourExchange234-audit.json. Preparation-time status below is historical.

# One-vertex exchange of a selected colour class

ColourExchange234.lean is prepared source with four intended axiom reports. It imports only Std and has not been compiled. No compiler, solver, or tests were run. The previous deletion-locality source was inspected, but its subset premise does not cover insertion; the present statements treat the exchange directly without a new graph definition.

Let $U$ be the old selected set, let $d\in U$, and let $a\notin U$. The exchanged set is

\[
U'=(U\setminus\{d\})\cup\{a\}.
\]

For an arbitrary label-to-vertex relation $C$, the selected-neighbour set of a label $z$ becomes

\[
N_{U'}(z)
=\bigl(N_U(z)\setminus\{d\}\bigr)
 \cup
 \begin{cases}
 \{a\},&C(z,a),\\
 \varnothing,&\neg C(z,a).
 \end{cases}
\]

The theorem exchanged_neighbours_iff proves this identity pointwise. It includes complete neighbour membership, so it retains the identities needed by contracted edges and endpoint attachments.

The theorem neighbours_unchanged_iff proves a stronger locality statement under the genuine-exchange premises $d\in U$ and $a\notin U$: the complete selected-neighbour set is unchanged if and only if $z$ is incident to neither $d$ nor $a$. For necessity, adjacency to $d$ removes an old neighbour that cannot be reinserted as $a$, while adjacency to $a$ creates a neighbour outside the old set. For sufficiency, every old incident vertex survives and insertion creates no new neighbour.

In particular, a label adjacent to both $d$ and $a$ has unchanged degree but a different neighbour set. Its contracted edge or singleton attachment must be updated. Caching only its degree would be insufficient.

## Singleton and internal labels

The theorem singleton_after_exchange specializes the exact identity to an old singleton neighbour $b$. The new neighbours are $b$ if $b\ne d$, together with $a$ if $C(z,a)$.

The theorem two_neighbours_after_exchange specializes it to two distinct old neighbours $b,c$. Remove either one equal to $d$, then add $a$ exactly when adjacent. The theorem does not assume that the updated label remains eligible internally.

For a finite selected set, write $t=|N_U(z)|$, $t'=|N_{U'}(z)|$, and let $\varepsilon_d,\varepsilon_a$ be the zero-or-one indicators of $C(z,d)$ and $C(z,a)$. Since the removed vertex was selected and the inserted vertex was outside,

\[
t'+\varepsilon_d=t+\varepsilon_a.
\]

This cardinality equation is a written consequence of the pointwise identity; it is not an additional Lean counting theorem in this module.

| Incidence to $d$ | Incidence to $a$ | Updated degree | Neighbour identities |
| --- | --- | --- | --- |
| No | No | $t$ | Unchanged |
| Yes | No | $t-1$ | Remove $d$ |
| No | Yes | $t+1$ | Add $a$ |
| Yes | Yes | $t$ | Replace $d$ by $a$ |

A new singleton can arise from an old degree-zero label by insertion, an old degree-one label with no net count change, or an old degree-two label by deletion. A new internal degree-two label can arise from old degree one by insertion, old degree two with no net count change, or old degree three by deletion. Therefore an enumeration based only on previously usable singleton and degree-two labels would omit possible new labels. Old degrees above three cannot become singleton or degree two in one exchange.

## Use in the finite enumeration

Only labels incident to $d$ or $a$ need their complete neighbour sets recomputed. All other labels retain both degree and neighbour identities. In a cube, the union of the two incident-label sets has size at most twice the dimension, so a selected-class exchange permits a small local update. This last numerical observation follows from the cube degree and is not proved by the generic relational source.

The pointwise statements apply both to singleton labels used as endpoints in the minority-class construction and to degree-two labels used internally. They do not construct a Hamiltonian path, establish endpoint-label distinctness, or validate a new snake. The fixed same-parity condition on $d,a$ and the complete literal relation $C$ must be supplied by the cube model.

The native bridge must preserve the same label universe before and after the exchange, examine all affected labels including previously unusable degrees, update neighbour identities even when the degree is unchanged, and retain the exact selected-neighbour conditions used by the accepted contraction constructors. Finite enumeration coverage and any resulting full-path witness remain separate evidence.
