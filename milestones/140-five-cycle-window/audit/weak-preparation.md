# Weaker count specialization: prepared source

The two new modules reuse the frozen `CycleBase140` CNF and its unchanged
refutation. No new solver search or proof export was needed. This preparation
ran no Lean process; the modules require separate checks.

1. `Weak140Semantics.lean` imports the already generated exact semantic module.
   It retains its window, meaning tree, ordered tags and raw CNF. The only new
   data are the relaxed bounds `[(3,3),(0,5),(4,4),(0,5),(3,3)]` and a counter
   list replacing unused slots 4 and 8 by the existing default endpoint
   counter. Its two expected axiom reports are `check` and `sat`.
2. `Weak140Actual.lean` additionally imports the original unsatisfiability
   module and the direction bridge. The canonical-frame proof is copied from
   the current exact-wrapper template. It combines the new semantic theorem
   with the original refutation, then derives the actual-snake statement.
   Its five reports cover the canonical frame, refutation, actual bridge,
   weak-count contradiction and final disjunction.

The proposed main theorem states that a fitting canonical `012032` window
with first, third and fifth internal counts 3, 4 and 3 satisfies

\[
6\leq\alpha_{r+2}\quad\text{or}\quad6\leq\alpha_{r+4}.
\]

It adds no parity, endpoint-location or coordinate-label assumption.

The preparation verifies the original frozen plan and all its source hashes,
then checks that slots 4 and 8 have no retained tag and that their 672 register
variables occur in neither a core clause nor any used counter's input list.
The earlier independent audit also found none in the retained proof.
Every used counter remains at its original index, with the same literals,
threshold and kind. The default counter has an empty list and threshold 2,
so its generic endpoint check is valid for any endpoint set. All elementary
counter conditions were independently evaluated against the relaxed bounds.
The full generic Lean tag check is still required.

`audit/weak-preparation.json` records input/output hashes, dependencies and
expected reports. `scripts/prepare_weak.py` writes only these new files and
refuses to overwrite them. The exact source, certificate and proof plan are
unchanged. The two modules can be checked separately: the semantic module is
independent of completion of the LRAT checks; the actual module requires the
final original unsatisfiability object.
