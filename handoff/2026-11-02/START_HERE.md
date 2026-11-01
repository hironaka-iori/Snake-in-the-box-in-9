# Ninth-dimensional Snake-in-the-box: continuation handover

Checkpoint date: 2 November 2026. Repository: `E:/Snake-in-a-box`.

The exact maximum remains unresolved. Length is measured in **edges**. The
project uses the interval **191 <= a(9) <= 235**, based on the checked 191-edge
witness and an inspected contributor theorem for 235. The full contributor
dependency closure has not been independently rebuilt here. The empty-square
route has a **conditional target of 234**, with explicit remaining local and
global proof obligations. There is no 196-edge construction or optimality proof.

This handover supersedes the continuation status in `handoff/2026-11-01/`.
That older record is retained as history. The main branch checkpoint preceding
this round is `cc332bf3c780d2e5adad7739eb9e1ed2f917fb2e`; the accompanying Git
commit records this handover and milestone74. `checkpoint.json` and
`file-manifest.json` identify the precise local evidence.

## Reading order

1. [Mathematical status](MATHEMATICAL_STATUS.md): definitions, bounds, completed
   results, and the distinction between finite-model and snake theorems.
2. [Next-agent prompt](NEXT_AGENT_PROMPT.md): a reusable continuation assignment.
3. [Milestone74](../../milestones/74-graph-interpretation-audit/README.md): exact
   graph indexing, contributor comparison, reusable proofs, and missing interface.
4. [Short-walk obstruction](../../milestones/74-graph-interpretation-audit/optimization/README.md):
   the latest result and six saved graph witnesses.
5. [Milestone73 continuation](../../milestones/73-countfree-share-catalogue/NEXT.md):
   proof-generation, replay, integration, and preservation commands.

## Latest completed work

- Ten local count-exclusion cases and the count-conditioned share-120 theorem
  are checked in milestone72. A count-free share-12 theorem for six distinct
  directions is also checked there.
- Milestone73 checks share16 for the patterns 012031, 012304 and 012314,
  including arbitrary coordinates and reversal. It checks complete coverage
  by nine six-transition patterns, the canonical adapter, the link from local
  shares to the global empty-square budget, and five-centre overlap.
- Milestone74 checks four direction-window shift identities and the algebraic
  short-walk obstruction in Lean. All five new printed axiom audits contain
  only the standard axioms. Previously compiled support is reused with hashes;
  this is not a fresh rebuild of the entire project.
- Six exact finite-graph tests show that removing the pending share rules, or
  retaining only the previously proved weaker rule for 012345, cannot recover
  conditional234 by changing the constant slope and potential alone. Witnesses
  were rechecked directly against the source arrays. This is a result about
  the present relaxed graph and boundary calculation.

## Pending proof preserved in detail

Case7305 concerns pattern012310 with share at least12. Its CNF, data,
structural module, all86 semantic clause batches and semantic composition
passed Lean: 92 modules in total. This proves the recorded clauses follow
from the local assumptions; a complete refutation and arbitrary-snake theorem
still require the selected proof replay and final geometric/reversal wrappers.

The original compact proof has224,393 derived clauses and12,625,945 hints.
Backward dependency slicing retains154,489 clauses and9,394,822 hints, with
all11,008 input clauses unchanged. The slot requirement remains15bits. The
selected proof, simulations, original proof provenance, semantic-preservation
checks and pending sources are recorded under
`milestones/73-countfree-share-catalogue/cases/case7305/`.
Consult that case's `data/pending-checkpoint.json` for the final saved state.
Simulation does not replace a Lean replay. Case7305 is not admitted to the
completed theorem catalogue at this handover.

No long replay is intended to be left running by this checkpoint. Inspect
actual processes and saved records before restarting any work. Session IDs
from old conversations are not reliable evidence of a current process.

## Local files and manuscript

The maintained repository paper is `paper/snake9_research.tex`. Its existing
editor mirror is
`D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`.
Both currently have SHA256
`d422a0b3dea2c2e81cb2d63294c14ff37b2237447faf5fca193ee2664951d341`.
The paper remains revision66; the next full rewrite was scheduled for76.
This round leaves the TeX files unchanged. The handover describes newer
research that has not yet been incorporated into the manuscript.

Authors, in order: **Iori Hironaka, Tommy Ma, Steven Zhan**. Preserve the
existing hyperlink metadata. Do not assign individual human authorship from
an AI-generated commit name alone. Branch provenance establishes where a
contribution appears; it does not establish how the three authors divided
their work.

Keep the manuscript mathematical. Proof-assistant file names, encoded tables
and implementation definitions belong in the reproducibility material.
When revising the open paper, edit its existing source and use the built-in
compiler. Do not replace the editor document or export an unrelated PDF.

## Environment and reproducibility limits

- Python executable:
  `C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`.
  Use `-X utf8`.
- Lean4.19.0 binaries:
  `D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin`.
  The pinned mathlib checkout is the adjacent `mathlib` directory.
- NumPy/OR-Tools packages: `work/solver_packages`; PySAT: `work/share_packages`.
- Some replay scripts contain these absolute paths and reuse pinned build
  caches. They must be adapted on another host. E: does not support the hard
  links used by some contributor scripts; use a checked copy overlay.
- Use the existing resumable drivers and source hashes. Never run two
  completion processes for the same case simultaneously. A wait timeout
  does not prove that the underlying compiler has stopped.
- Preserve exact audited bytes. The milestone `.gitattributes` files prevent
  line-ending conversion of hashed Lean sources, logs and JSON. Large generated
  sources and compact proofs are archived separately from compiled caches.

Unrelated local changes in `.gitignore` and
`milestones/50-three-count-return/excess-screen/data/critical-family.json`
are preserved. Other untracked research also remains in the repository.
Avoid broad staging, resets, cleanup or replacing those files.

## GitHub and other branches

The remote was fetched during this round. The examined contributor branch
`research/unconditional-241` remains at
`cd0c90fddf12170d735ee34fcc501e99c60632a6`. Its `UpperBound234` source uses the
final B234 keys, but the saved composition relied on temporary proof stubs for
unfinished production pieces. It is not evidence of a completed bound234.
Milestone74 pins the relevant source and explains the distinct seven-centre
count-only model. `checkpoint.json` records the other fetched branch tips.

The accepted235 evidence is pinned in
`milestones/51-exact-bucket-pressure/data/repository-check.json` and its
`data/contributor/` snapshots. Keep its contributor-checked status separate
from a fresh independent rebuild.

The next useful result is either a fully audited case7305 theorem or a checked
actual-snake interpretation of the exact history graph. A new numerical bound
requires both the relevant local premises and the global proof chain.
