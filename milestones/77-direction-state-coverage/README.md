# Milestone 77: actual direction states and history compatibility

The exact optimum remains unresolved. The maintained project interval is
191 through 235 edges, with 235 inherited from the inspected contributor proof
and saved audit. The target 234 still requires six local share targets,
complete graph interpretation and full potential replay.

## Checked interface

All 36 modules passed, with 106 printed theorem audits. The successful current
receipts are collected in `data/proof-summary.json`. Every receipt identifies
its exact source, compiled object, dependencies and log. The checked interface
is as follows.

- Every canonical induced eight-direction word belongs to the ordered
  132-entry state list; every such nine-direction word belongs to the ordered
  505-entry extension list. The result applies to arbitrary actual snake
  windows, using the inherited geometric interpretation.
- The resulting numeric IDs are in range and decode to the actual canonical
  directions. Computed source and target IDs agree with consecutive actual
  eight-direction states. For m>=9, the direction sequence has m-8 edges and
  m-7 states, including the terminal state.
- Round-trip uniqueness and the recorded source/target maps agree with these
  definitions. The ordering is oriented and canonical; reversal classes are
  not the same IDs.
- The numeric history index is below 75, decodes to its longest dictionary
  suffix, and starts at zero. A listed signature is a suffix of the actual
  updated history exactly when it is a suffix of the stored updated history.
  The generic lemma requires the signature's proper prefix in the dictionary.
- Every nonempty actual history has the actual current direction shape. The
  recorded compatibility filter is correct at the source and target of each
  valid actual direction step. The zero history has no shape restriction.

No theorem here identifies the builder's concrete numeric history selector
with that history index, assembles the complete count/history state, proves
membership in the retained edge list, interprets every exclusion and credit,
or supplies the complete potential proof. Consequently this milestone gives
no improved numerical bound and no completed new local share case.

## Finite checks and resource use

An independent executable audit enumerates 4,140 restricted-growth words of
length eight and 21,147 of length nine. Exactly 132 and 505 are induced and
match the saved lists in order. It also checks 37,875 history/direction updates.
That executable evidence is separate from the Lean coverage and interface
theorems.

The monolithic coverage check required excessive memory. Its replacement
rejects a non-induced prefix only after proving that no induced completion
can have that prefix. It checks twelve six-direction branches; the largest
branch is divided into seven seventh-direction cases. The lookup checks use
six consecutive index blocks. Every finite branch and assembly step is checked
by Lean's kernel; Python generates the source and supplies no proof axiom.

`diagnostics/` preserves the superseded sources, resource observations and
receipts. Interrupted computations establish no mathematical conclusion.
`audit/final-scope-review.md` and `audit/handover-review.md` are independent
source reviews at their recorded snapshots. Current successful receipts
supersede their earlier pending-status observations. Their caveats about
global scope remain applicable.

Lean4.19.0 reports only `propext`, `Classical.choice` and `Quot.sound` where
axioms occur. No proof placeholder or unchecked native decision is used.
Inherited compiled support is reused after hash checks; its entire dependency
closure has not been rebuilt in this continuation.

## Reproduction

From `E:/Snake-in-a-box`, use the installed Python runtime with `-X utf8`.
The exact runtime and inherited object paths are recorded in the scripts and
receipts. Run the modules in this order with `scripts/check.py MODULE`:

1. `DirectionTables`, `PrunedEnumeration`, `PrunedAssembly`.
2. `CoverageLeaf00` through `CoverageLeaf10`, `CoverageTail00` through
   `CoverageTail06`, then `CoverageLeaf11`, `CoverageAssembly`, `DirectionCoverage`.
3. Run `history/scripts/check.py` for `NumericHistory`, then `ActualDirectionIds`.
4. `LookupDefinitions`, `LookupChunk00` through `LookupChunk05`, `LookupTableCheck`.
5. `HistoryCompatibilityData`, `HistoryShape`.

The source generators are `prepare.py`, `prepare_chunks.py`,
`prepare_lookup_chunks.py` and `prepare_compat.py`. Reuse unchanged successful
receipts after validating their hashes; a fresh run is necessary after a
relevant source or dependency changes. Run heavy finite checks sequentially.

`scripts/finalize.py` validates every current receipt and freezes successful
case7305 rows without altering its live files. `scripts/verify_saved.py`
creates the local manifest; `--verify` checks it and `--staged` also checks the
Git index. The build folders remain local and are excluded from Git.

## Handover

The current entry point is `handoff/README.md`, with mathematical status and a
reusable continuation assignment alongside it. `data/checkpoint.json` and
`replay-snapshot/record.json` record case7305's observed progress. They are
historical observations; inspect the actual process before restarting and use
one completion driver per case. The saved tool session is 41012.

The paper remains revision76 and its editor/repository copies are unchanged
and hash-matched. The current compiler retry again failed before source
compilation; `data/editor-compile.json` preserves the diagnostic. No alternate
document or PDF was created.
