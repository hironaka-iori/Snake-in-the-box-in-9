# Cross-contact necessity for a simultaneous escape: prepared source

Status: source prepared only. No compiler, solver, native worker or software tests have been run. The accepted `TwoBlocks224` source is unchanged.

The new theorem `escape_requires_cross_contacts` imports `TwoBlocks224` and introduces no definitions. It quantifies over a family of actual indexed induced paths of fixed edge length `n`, a maximum individual block length `K`, and an extension predicate on those paths.

The closure premise explicitly says that any actual induced path obtained by changing only the open interior of a bounded interval of length at most `K` remains in the family. The blocked premise says that family members do not satisfy the extension predicate. The initial path is in the family; the final path satisfies the extension predicate. Both paths agree outside two ordered bounded open intervals `(a,b)` and `(c,d)`, and each interval has length at most `K`.

The conclusion provides two pairs of indices, which need not be the same pairs:

1. A new vertex in the first interval equals or is adjacent to an old vertex in the second interval.
2. An old vertex in the first interval equals or is adjacent to a new vertex in the second interval.

The adjacency orientation follows increasing block order. For an undirected graph this states cross-contact in both replacement directions. Equality remains an allowed contact and is not silently replaced by adjacency.

If the first contact were absent, the accepted geometric constructor produces the intermediate using the final path in the first interval and the initial path elsewhere. Closure applies first to the first block and then to the second, putting the final path in the blocked family, a contradiction. If the second contact were absent, apply the same constructor with the initial and final paths exchanged. The resulting intermediate uses the final second interval and the initial first interval; closure applies in the reverse order and gives the same contradiction.

Both intermediate paths are supplied by the accepted actual-path constructor, not assumed valid. All outside-index equalities needed by closure are derived from their explicit vertex formulas and the given agreement. The proof uses no numerical bank property, solver result or assumption that already asserts the required contacts.

Application to the saved bank still requires its native short-move closure and blocked-extension premises, including the stated allowed block lengths and symmetry treatment. This source does not convert that enumeration into a Lean certificate. It does not assert existence of a simultaneous escape or give a new snake bound. One exported axiom report is requested; compiler acceptance remains pending.
