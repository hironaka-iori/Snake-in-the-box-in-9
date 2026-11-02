# Milestone 85: exact reference catalogue union

The 1,378 reference patterns used by the current comparison graph are connected
to the two pinned contributor catalogues. Conditional on their closed
refutation statements, every actual snake passes all corresponding reference
filters, in both orientations and at every fitting position. Twenty-seven
modules passed Lean 4.19.0 with 103 printed theorem audits.

The two closed catalogue premises remain explicit. This result establishes
neither a new global bound nor a completed proof of the target 234. The project
interval remains 191 through 235 edges, with the upper bound supported by the
inspected contributor theorem and saved audit rather than a fresh complete
independent rebuild.

## Exact union and theorem

The catalogue associated with 235 contains 1,287 keys; the catalogue associated
with 236 contains 732. Their intersection has 641 keys after simultaneous
reversal of directions and counts and canonical coordinate relabelling. Thus

\[
1287+732-641=1378.
\]

Every chosen canonical representative occurs directly in one of the original
source lists. The exact selection takes all 1,287 keys from the first list and
91 additional keys from the second. Expanding orientations gives 2,678 distinct
direction-and-count pairs. The widths are two through six count positions;
the numbers of canonical keys by width are 4, 43, 213, 1,076 and 42.

For a snake with m edges, take a nine-direction window starting at r, where
r+9 is at most m. A reference key with w counts fits at offset s when s+w is
at most six. Its directions start at r+s+2; its counts are the actual singleton
counts at positions r+s+3 through r+s+w+2. Count symbols one through five mean
exact equality; symbol six means the interval [6,21].

The checked theorem excludes a match of either the forward key or its joint
direction-and-count reversal. It uses the count-slice, saturation, coordinate
normalization and reversal lemmas already checked in milestone 79. The finite
part proves each source index is valid, each selected key is exactly the
indexed source key, every key has valid width and symbols, and the assembled
list has length 1,378. These checks are split into 22 small tables to avoid
repeated searches through the full source lists.

The final theorem has exactly the two named local catalogue-refutation
premises in addition to its snake, membership and fitting-window hypotheses:
`AllRefuted6K235` and `AllRefuted236`. Compiling their key-data definitions does
not discharge either premise. The saved provenance report identifies the
closed source theorems and the historical Linux audits. Matching compiled
closed proofs were absent from the searched local locations.

## Executable comparison and limits

The reference-filter loop is extracted from the current graph builder. A
separate implementation uses the literal Lean keys and direct digit folding
to compare its count selection with the builder's quotient/remainder slices.
All 505 direction extensions and all 46,656 count codes are tested:
23,561,280 pairs, with 7,278 applicable pattern placements across the direction
extensions. The isolated filter accepts 3,899,352 pairs and rejects 19,661,928.
These numbers do not count newly removed edges in the full graph.

The Python implementations share canonicalization conventions and the stated
direction offsets. Their agreement independently checks the count slicing
and table equality; the semantic connection to actual snake positions is
provided by the Lean lemmas and source review. Python execution is separate
from the Lean proof. The mask and all comparison inputs have saved hashes.

All 103 printed theorem audits contain only subsets of `propext`,
`Classical.choice` and `Quot.sound`. The inherited window environment is reused
with source, object and log checks. Its full dependency closure was not rebuilt.
The bounded independent review records its scope and the exact source snapshots.

## Reproduction

Run the scripts from E:/Snake-in-a-box using the saved Python runtime and Lean
4.19.0 environment. The scripts use pinned local support and absolute runtime
paths; another host must restore or rebuild that support and adapt the paths.

1. `scripts/prepare.py` preserves the three pinned upstream sources and checks
   the exact source/JSON union.
2. Run `scripts/check.py LocalWindowDirKeys6K235` and
   `scripts/check.py LocalWindowDirKeysR4` for the two data-only modules.
3. Run `scripts/check_interface.py`, then `scripts/check.py ReferencePicks`.
4. `scripts/generate_chunks.py` creates the 22 finite tables and assembly.
   Run `scripts/check.py` on ReferenceChunk00 through ReferenceChunk21 in order,
   followed by ReferenceUnion.
5. Run `audit/check_builder.py`, then `scripts/finalize.py` after the independent
   review has been saved. The finalizer also freezes a live case7302 observation.
6. Use `scripts/verify_saved.py --verify` to check an existing frozen manifest;
   run it without that flag only when deliberately saving a new checkpoint.

Sources, successful receipts, logs, exact upstream bytes, independent review,
comparison mask and current handover are saved. Build objects remain local.
Earlier manifests identify historical versions of shared handover files.

## Remaining work

The ten interval filters, forty short filters and three history exclusions
already preserve actual snakes. The reference family now has an exact checked
union and conditional retention theorem. Its two closed catalogue premises,
the exact retained-array index, interpretation of every applicable credit,
and the complete potential check remain separate obligations.

Case7302, the count-free share-20 target for 012034, continues under its existing
driver. Inspect its actual process and saved records before resuming; do not
start a duplicate. The four completed target cases and five pending target
cases remain unchanged. The current paper is revision 76; the next full
revision is scheduled for milestone 86.
