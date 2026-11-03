# Milestone 129: the fourth count equal to three

The fourth-count-three case of the 0120324 window now has a complete native
contradiction, independently replayed through all 50082 deductions. Its
3500 selected clauses use fewer hypotheses than the original search, supporting
the candidate implication

$$
\alpha_{r+4}=3\quad\Longrightarrow\quad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge12.
$$

Lean checks the exhaustive case split, the actual-snake count conversions,
and satisfaction of all 3500 clauses under the contrary hypotheses. It also
checks the triple lower bound and the equality-case six-count lower bound 23
conditional on the contradiction of this exact input. These four modules
have 17 successful axiom reports. The complete 221-module Lean refutation is
still running. The candidate implication therefore remains unproved without
that remaining premise. See milestone 129's mathematical note and verification
record for the exact saved progress.

The earlier endpoint batch has also completed. An independent audit verifies
all 448 modules and 30 axiom reports. For a fitting canonical 012032 window,
equality of the second and fourth counts' sum to eight forces both centres
to have Hamming distance two from both endpoints. There are at most thirteen
such starts in any snake. The final theorem has no remaining local-certificate
premise. This occurrence bound needs a further global argument before it
can improve the upper bound on snake length.

The complementary fourth-count-at-least-four case remains unresolved. No
universal six-count bound or improved global upper bound is claimed. The
maintained interval remains 191–235, with the documented independent-rebuild
limitation on the contributor upper-bound proof. The optimum and 196 remain
open. No new mathematical definition is introduced. Paper revision 126 is
unchanged; the next scheduled full revision is 136.

## Saved evidence

- MATHEMATICAL_NOTE.md gives the argument using the existing notation.
- audit/branch-input-review.md checks the new input and full native proof.
- audit/transport-review.md checks every reduction and input mapping.
- audit/export-review.md independently checks all selected clauses, meanings,
  packed deductions, checkpoints, slot reuse and exported source changes.
- audit/core-semantics-derivation.md records the checked actual-snake meaning.
- audit/endpoint122-completion-review.md records the completed endpoint theorem.
- archives/endpoint122-completion-*.tar.gz preserves all 1528 newly completed
  endpoint evidence files that were absent from the repository index.
- data/proof-plan.json pins the 221 exported Lean modules.
- data/replay-progress.json is the live local progress; the frozen observation
  in audit/observed-replay129.json records the checkpoint's exact prefix.
- data/verification.json and data/file-manifest.json identify the saved bytes.
- archives/ preserves the native traces and original generated sources as
  separately verified lossless gzip files; the raw local files are retained.

Run scripts/verify_saved.py --restore-archives after a fresh checkout, then
scripts/verify_saved.py --verify. Inspect the process and replay.lock before
resuming scripts/run_replay.py --timeout 600. Never start a duplicate worker
or remove a live lock.
The driver reuses verified receipts and waits for sufficient resources.

The first replay attempt encountered a Lean import-root lookup error before
checking Data0. A verified byte-identical copy of the CNF object into the
replay build directory fixed it. The failed attempt is retained. The original
generated sources use CRLF; the ported sources use LF, with the exact change
independently checked and recorded. No unrecorded source normalization was made.
