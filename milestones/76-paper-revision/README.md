# Milestone 76: paper revision and conditional arithmetic

The existing manuscript now integrates milestones 67–75. Its argument proceeds
through local shares, overlap accounting, the improved boundary estimate,
exact history recognition, current graph comparisons and remaining obligations.
Superseded model calculations remain in an appendix.

The project interval remains **191 through 235 edges**. The target **234 is
conditional**; the exact optimum and conjecture 196 remain unresolved.
The strengthened charge budget and proposed potential give

\[
W+4200m\le1098960,\qquad496(m-8)\le W+600,
\]

hence 4696m≤1103528. This excludes 235 with margin 32, provided the six pending
local shares, complete arbitrary-snake graph interpretation and full potential
replay are supplied. The completed-share comparison still gives 235.

## Manuscript and checks

The existing paper is `E:/Snake-in-a-box/paper/snake9_research.tex`; the open
editor source is `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`.
Their bytes match. Iori Hironaka, Tommy Ma and Steven Zhan remain the authors,
and the entire preamble, including hyperlink settings, is unchanged.

- All 116 earlier statement blocks are preserved; seven additions give 123.
- All 13 printed paths pass 118,673 vertex-pair checks. The 175-row old exclusion
  table is unchanged; all 180 labels and bibliography references resolve.
- Six fresh Lean 4.19 arithmetic checks pass with only the standard audited
  axioms. They are conditional implications, not a complete global rebuild.
- The independent audit read all 3317 original lines and reviewed the additions.
  The old three-twos discussion remains an explicit outline. The written
  converse-emission argument is distinguished from the checked invariant and
  soundness results.

The built-in compiler failed before source compilation because its Windows
helper could not prepare the execution environment. The exact diagnostic is
saved in `data/editor-compile.json`. No new PDF or page-layout verification is
claimed. No alternate document or PDF was created.

## Continuation

Case 7305's unchanged replay remained active at the checkpoint. Inspect
`data/checkpoint.json`, the frozen successful rows under `replay-snapshot/`,
and the actual live process before acting. The saved tool session is 41012.
Do not start a duplicate completion driver. Partial module success does not
establish its final share theorem.

After the existing refutation succeeds, finish full completion, geometry and
reversal, the axiom audit and archival. The next global step is the exact
arbitrary-snake graph walk, followed by full potential replay. The current
entry point is `handoff/README.md`; the earlier detailed handover remains at
`handoff/2026-11-02/START_HERE.md`. Contributor commit 1e0ebb95 still records
unfinished 234 production work.

## Reproduction

Use the installed Python runtime with `-X utf8` from the repository root.
`scripts/revise.py` reconstructs the revision from its exact baseline and refuses
unrecorded edits. `scripts/verify.py` checks preservation, witnesses, arithmetic
and the small complete shape enumeration. `scripts/check_arithmetic.py` runs
the six Lean checks. `scripts/checkpoint.py` freezes successful replay evidence.
The `audit/` directory contains the independent reports; `text/` contains the
two manuscript additions. Existing runtime and support paths are host-specific.
