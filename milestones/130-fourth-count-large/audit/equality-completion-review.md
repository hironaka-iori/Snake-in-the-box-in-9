# Independent review of the completed fourth-count-three case

Result: `PASS_COMPLETE_EQUALITY_CASE_ACTUAL_SNAKE_AUDIT`. The review finished on 3 November 2026 at 21:45:11 JST. The saved replay covers all 221 planned modules and all 435 proof segments for the selected 3,500-clause formula. The actual-snake assembly has passed compilation and exposes three results without an unresolved refutation premise.

For an actual snake, assume the seven directions beginning at position \(r\) fit within the snake and have canonical form \(0120324\). The first two results additionally assume that the fourth count is exactly 3:

1. The counts at positions \(r+3,r+5,r+6\) sum to at least 12.
2. The six counts at positions \(r+1,\ldots,r+6\) sum to at least 23.
3. Under the fitting-window and canonical-shape assumptions alone, a six-count sum at most 22 forces the fourth count to be at least 4.

The first result has no six-total or pair-count premise. The second consumes the checked semantic helper and the completed refutation. The third combines the second result with the previously checked split theorem. The exact Lean declarations are saved in `data/equality-completion-review.json`, under `actual_source`; the source is `lean/ActualFourthThree130.lean`.

## Evidence checked

The audit independently checked the terminal `PASS_COMPLETE_CNF_REFUTATION` status and exact 221-module coverage; each receipt, source, compiled object, compiler log, source snapshot and checker snapshot; all recorded dependency hashes; and the resolved direct imports against the saved search paths. It inspected the selected CNF source pin and its 3,500 raw clauses and tags, the concrete semantic helper, the actual split helper, and all three final theorem statements and premises. All 435 segment theorems occur and are consumed once by the final contradiction assembly. The contradiction declaration is `theorem unsat : Unsat cnf`, with no external refutation assumption.

The plan and execution lists contain the same 221 modules, but their sequences differ. Both are valid dependency orders. The execution list equals the depth-first source-import order independently reconstructed by the auditor. Consequently, the differing sequence is recorded explicitly and does not indicate missing coverage.

The final contradiction and each of the three actual-snake theorems report exactly `propext`, `Classical.choice`, and `Quot.sound`. The inspected source files contain no `sorry`, `admit`, `native_decide`, or new `axiom` declaration. All 1,336 unique input files were hashed again at the end and were unchanged. The JSON records every pass criterion, all module reviews, both complete module orders, and the complete file-to-SHA256 map.

This is an independent inspection of saved compiler evidence and dependency identities. This reviewer did not rerun Lean, native proof replay, a solver, or an archive operation.

## Scope

The equality case is now complete at the actual-snake level. Earlier frozen milestone129 records describing a pending replay remain historical records; the terminal replay receipt and milestone130 assembly provide the completion evidence.

The complementary case with fourth count at least 4 remains unresolved by this result. A six-count lower bound of 23 for every canonical \(0120324\) window does not follow. No new global upper bound on the snake length is claimed.

## Audit attempt record

The first reviewer invocation, tool session 37479, stopped at an assertion in the reviewer's axiom-name parser. It had treated a short `#print axioms` name inside a namespace as a fully qualified name, while the saved compiler output correctly printed the full name. The parser was corrected to track namespaces. The completed run, session 94371, passed in 23.203 seconds. The unsuccessful invocation produced no review JSON and changed no proof evidence. This paragraph preserves the unsuccessful attempt and its cause; no compiler or mathematical failure was observed.

## Principal SHA256 values

| File or object | SHA256 |
| --- | --- |
| `data/equality-completion-review.json` | `cfbce3f946f1eca3164ef5dd2cf2863bad59842d7e278bee82ca0cf9446b0806` |
| `audit/check_equality_completion.py` | `1eff697e4b58e77919fe2513359e7ce5c207f3fc72482f755c065d543090a3ec` |
| milestone129 final refutation receipt | `3b86a6a1e1ee8dce463ea7a465ae3cfa0af39183dc11523bab27cb17eecd8757` |
| milestone129 final refutation source | `3464e27251ba3df35c2d8af4d18a937bda963d2e1c2e989b33a3789dfc4139e2` |
| milestone129 final refutation object | `4a0659ee5abe8dd7f811c2592e35075c3aaf64f5688a15c4805cbece38b7b424` |
| `data/independent-actual-final-audit.json` | `e982cbec254b76994c02aed9fd188f842c20ffea7796c0657bf7fddb588efcd1` |
| `lean/ActualFourthThree130.lean` | `a980181da91cdd7347d46c9382d0b160faf4bed499c55a205cbe037788d96def` |
| actual-snake compiled object | `500f27f505dea824dad5b61057b144704a3ebbf3835c99368308998e8f9d9f1a` |
| actual-snake compiler log | `921aca94c428611a0a8c9c6bccb6d1e4bb21e889fca17317e29209f9945380aa` |
| `scripts/check_final.py` | `c8c99b2d0b1d5b6ca3f1cc669ee9cf4f3cb45e2f48a4afd2a86a8baa15a33958` |
