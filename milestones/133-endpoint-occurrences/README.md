# Milestone 133: sharpness and endpoint occurrences

Two concrete counterexamples have passed Lean. A 149-edge odd snake attains
pair counts 6 and 3 in a canonical 012032 window. A 133-edge odd snake attains
counts 4 and 5. Thus the pair floor cannot be raised uniformly to ten, even
when both counts are at least four. These are auxiliary sharpness examples,
not improvements on the 191-edge construction or realizations of a full
periodic critical cycle. Neither example decides a length 235-only restriction.

The first witness's window starts 130 edges after its qualifying endpoint.
The second is 106 edges from its qualifying final endpoint. Hamming proximity
therefore cannot be replaced by a short distance along the path.

A written geometric argument bounds the number of assigned windows at one
endpoint by twelve, or eleven when no counted window includes that endpoint.
It uses the common coordinate in the alternating window vertices and the
absence of the opposite pair between consecutive such vertices. The interval
packing lemma and final conditional arithmetic have passed Lean. The transfer
from an actual snake to the full geometric counting argument remains pending;
the occurrence theorem itself is not yet Lean-checked.

The endpoint 0 search returned native UNSAT with no cycle cuts. Its exclusion
has no checked certificate and must not be used as a theorem. The other two
searches produced the fully checked witnesses. All inputs, models, valid cuts,
native reviews, compiler attempts and successful receipts are retained.

Next selected task: complete the actual-snake geometric occurrence proof.
Do not replace it by another uniform pair-floor proposal. The recorded global
interval remains 191–235 with the existing incomplete independent upper-proof
rebuild; the optimum and 196 remain open. Paper revision 126 remains unchanged,
with the next full revision due at 136. Only notation needed repeatedly in
the counting proof is introduced.

## Saved material

- MATHEMATICAL_NOTE.md separates proved counterexamples from the written count.
- lean/Witness133.lean and BalancedWitness133.lean contain the two checked paths.
- work/probe-endpoint18 and work/probe-balanced retain all models and reviews.
- work/probe-endpoint0 retains the uncertified boundary exclusion result.
- audit/occurrence-geometry.md contains the written geometric proof.
- lean/IntervalPacking133.lean and OccurrenceArithmetic133.lean contain the
  checked general and conditional lemmas.
- data/*-audit.json records successful compiler runs and exact dependency hashes.
- data/verification.json, checkpoint.json and file-manifest.json fix this save.

Do not restart completed probes or checks. The separate milestone115 proof job
must be inspected through its live process and lock before any restart.
