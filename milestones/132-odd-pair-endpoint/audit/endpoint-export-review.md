# Independent export and semantic-source review

Result: `PASS_BOUNDED_ENDPOINT_EXPORT_AND_STATIC_SEMANTICS_REVIEW`. The exported contradiction preserves the previously audited original core. The variable transport, generated dependency graph, packed data, semantic tables, and final theorem statements passed the bounded independent checks. This review did not run Lean or a solver and does not certify completion of the separate compiler runs.

## Variable transport and selected clauses

The explicit old-to-new map and its inverse are bijections of all 2,426 variable IDs. The 311 variables active in the selected clauses or proof deductions occupy the first 311 new IDs, in the specified sorted order. This keeps all proof literals below the checker's offset of 2,400. Every one of the 96,552 original input rows was checked under the same signed-literal transport. Every original and renamed LRAT deduction preserves its clause ID and ordered hint list.

All 683 original selected clause IDs, literal lists, signs, tags and occurrences agree with the frozen original-core audit. The generated Lean CNF was reparsed and equals that transported core: 676 base clauses followed by the seven negative endpoint units. The units still concern vertices \(0,10,18,34,66,130,258\). Neither positive parity clause is present.

Counter 1 retains exactly 42 literal occurrences over 37 distinct primary variables, with bound 9. Counter 0 is a dummy entry; the selected clauses do not use it. The semantic proof derives the meaningful counter's bound from the actual pair-count premise. Its stored kind label does not supply an endpoint-count assumption in that proof.

## Packed proof and generated modules

The 51 planned modules form a closed, acyclic internal import graph. The only external imports of this generated group are `LratFast` and `LocalWindowDirModel`. All planned source hashes matched. The 50 retained generated-source snapshots differ from their emitted versions only by the intended isolated import prefix and the final axiom-report command. The separate CNF module was checked directly.

The reviewer decoded the emitted packed numbers independently of the generator. All 13,299 deductions and 554,859 hint references match the transported LRAT in order, through slot reuse and all checkpoints. The checks covered:

- 93 proof segments and all 93 segment theorem declarations;
- 23 checkpoints containing 47,081 packed entries;
- 1,119 allocated slots in the height-11 tree;
- 13-bit packed words and literal offset 2,400;
- final empty clause in tree slot 1,024;
- exact use of every segment theorem once in the final contradiction assembly.

Nonzero checkpoint entries equal the clauses occupying their slots at that point. Entries discarded at a checkpoint are never silently substituted for later hints: each later hint was checked against its original transported clause ID. Literal and hint lengths remain below the checker's respective fuel limits. This checks the packed representation against the already replayed native proof; it does not repeat the native propagation replay.

## Semantic tables and theorem statements

The final repaired `CoreSemantics132.lean` source has SHA256 `eed0322cdf8ebad2eae5e6efddaed4893440583d7a844cc6b8f28a8e06f7103e`. All 1,252 supplied meanings were decoded from its tree and checked against the transported meaning table. Every variable used by the selected clauses, deductions or meaningful counter has one of these checked meanings. The 11 raw-clause and tag chunks reproduce all 676 base clauses in order. The seven unit literals map to the intended endpoint flags with negative polarity. The pair-corner comparison uses a list permutation, preserving multiplicity.

The source `ActualEndpoint132.lean`, SHA256 `573b0366c7dd40f141634f8721d49e64710b6677ba4c9a4ca33ef6704c5dc9bf`, declares:

1. For a fitting canonical \(012032\) window and pair count at most 9, there exists an index \(k\in\{0,m\}\) such that the same vertex \(p_k\) is at Hamming distance 2 from both internal centres.
2. If neither endpoint has both distances equal to 2, the pair count is at least 10.

Both declarations have the expected induced-path, fitting-window and canonical-shape assumptions. Neither has a length-parity assumption, a start-parity assumption, or an external unsatisfiability premise. The final source explicitly supplies `Endpoint132.unsat` to the conditional semantic bridge. It transports a single normalized endpoint back to the original snake before proving both distances, preserving the required quantifier strength.

## Preserved attempts and limits

Two reviewer conditions were repaired during this audit. The first attempt incorrectly required zero meanings at every unused ID up to 2,426. The semantic tree intentionally supplies only the 1,252 required meanings; its leaves can alias larger unused indices. The corrected check verifies the entire supplied range and every actually referenced variable. The second attempt parsed the tag name `deg2` as `deg` with argument 2. The tag-name parser was corrected, after which all tag chunks matched. Neither issue changed the exported evidence.

These reviewer repairs are distinct from the semantic source's compiler failures. The first source attempt had unresolved list-membership and singleton-clause steps. Repair 1 left the Boolean goal `(!false) = true`; repair 2 added its final `rfl`. The final review pins `semantic-repair2.json`, the repaired source and generator, both failed compiler logs, and both preserved failed-source snapshots. The provisional static review of repair 1 remains nested in the final JSON. A static statement/table check does not imply that the source compiles.

The complete refutation, semantic-module and actual-snake compiler receipts, their axiom reports, and their dependency identities are outside this bounded export audit. The coordinator handles that completion review separately. This bounded review establishes no endpoint-occurrence budget or global snake bound. All original audited files and all compiler evidence were left unchanged.

The final JSON records 81 fixed input hashes and the complete final theorem source. All fixed inputs were rehashed at the end of the audit.

- `data/endpoint-export-review.json`: SHA256 `ed670530e763f196c6208195d68464d3c83ac0b4dc9c3d2c0b7c9223b72432cc`.
- `audit/check_endpoint_export.py`: SHA256 `f81ab7f21c3cbc7695b6cbcd535a7e0bb6a88cc77d0dc55dfa166f20e916c1b9`.
