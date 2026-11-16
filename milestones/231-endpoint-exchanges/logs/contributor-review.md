# Contributor branch review: conditional 231 chain

The maintained manuscript interval should remain **191 <= a(9) <= 233** on the evidence inspected. The new material targets a whole-Q9 upper bound of 231 and reports that its conditional Lean 4.35 chain builds. It does not contain an inspected completed unconditional 231 assembly. This is an outstanding certificate/assembly issue as well as an independent-rebuild limitation.

## Pinned scope

- Repository: `E:/Snake-in-a-box`.
- Reviewed remote-tracking snapshot: `origin/research/unconditional-241` at `5309471b80154eff6f9a247a8edb0e865403d9f7`.
- Comparison base: `55915593bebeef90db684a89b6196025f82a3e03`.
- Highlighted commit: `d136273923c9c5982bd16861d8a4f833af0ab864`, dated 2026-11-15 16:32:40 UTC, titled “lean435: the 231 chain (563B1, plan 563_1_cap) builds in 4.35; summary and shard hashes”.
- Inspection used read-only Git object access and small exact arithmetic. No fetch, merge, import, compiler, solver, proof replay, process change, or manuscript edit was performed. Other transfer branches and external worker artifacts were not inspected.

## Exact numerical claim and applicability

`milestones/35-231-lean/scripts/gen_lean_chain6sc.py`, lines 233–240, together with `lean435/data/auto6sc_563B1.json`, specifies the following conditional interface:

```lean
Snake9.upper_231_of_refuted6SC563B1 :
  Snake9.LocalWindow.AllRefuted6S563B1 →
  Snake9.LocalWindow.AllRefutedShare6S563B1 →
  Snake9.LocalWindow.AllRefutedCtx6SC563B1 →
  Snake9.DirectionWindow6S.Floors233 →
  ∀ {m : Nat}, Snake9.Snake m → m ≤ 231
```

This interface is reconstructed from the generator and saved parameters; an actual generated `AggregateDirection6SC563B1.lean` theorem body was not present in the inspected tracked tree. The first premise packages plain and H8 refutations; the contextual premise packages both contextual lists. These premises must be discharged, rather than treated as arbitrary assumptions of an unconditional result.

The summary has `P = 563`, `Q = 1`, `B = 10`, `bound = 231`, and `toy = false`. The reported native potential range is 1022; the theorem's range allowance is `2^10 - 1 = 1023`. The generated comparison is

\[
4763m\le1099800+7\cdot563+1023=1\,104\,764.
\]

Since

\[
4763\cdot232=1\,105\,016=1\,104\,764+252,
\]

the integer conclusion is indeed `m <= 231`, provided all the premises are established. This arithmetic was independently recomputed.

The applicability is genuinely whole-Q9. `work/final_lean/Snake9.lean` uses `Vertex := Fin 512`, adjacency by one of nine bit flips, and an injective indexed path whose adjacency is exactly consecutiveness. There is no saved-seed, endpoint, crossing-count, or replacement restriction. `work/spectral/stronger/AggregateDirection6SCConditional.lean`, particularly `upper_of_refuted6SC` at lines 78–91, takes any such `Snake m`; the window aggregation also handles the small-length case. The obstacle is completion of its certificate premises, not a hidden constructive-family restriction.

## Evidence actually available

1. **The highlighted commit adds generation metadata only.** Its two files are `lean435/data/auto6sc_563B1.json` and `lean435/data/shards6sc_563B1.sha256`. The latter records 205 source hashes: one data module and 204 shards. The summary reports 10,404,288 checked transitions, 3,035,269 allowed canonical transitions, 31,902 plain keys, 262 H8 keys, 1,714 share keys, 2,797 context-seven keys, and 440 context-eight keys. These describe the generated chain and its required coverage, not completed refutations of every listed case.

2. **The saved plan is pinned correctly.** The Git blob of `milestones/28-combined-identities/data/certplan231_563_1_cap.json.gz` has SHA-256 `d6ed4945cee40d2f729e4b695b1edf04f7315281bf29b9970909f1cb638ae172`, agreeing with the summary. No native optimizer or transition scan was rerun here.

3. **The build claim is conditional and contributor-reported.** `lean435/tools/chain435.sh` generates, ports, and builds the conditional chain before preparing glue. The inspected tracked tree contains no 563B1-specific final theorem audit log, completed unconditional 231 source, or accepted final assembly receipt. Generated sources/builds are also used outside Git; their absence from this snapshot is not evidence that no external artifacts exist.

4. **Assembly tooling has a proper full-completion distinction.** `lean435/tools/assemble435.py` has a partial `--chunks` mode that audits only chosen chunks. Its full mode builds all glue, then generates an unconditional theorem of the shape

   ```lean
   public theorem upper_231_435 : ∀ {m : Nat}, Snake m → m ≤ 231 :=
     upper_231_of_refuted6SC563B1 LocalWindow.allRefuted6S563B1
       LocalWindow.allRefutedShare6S563B1
       LocalWindow.allRefutedCtx6SC563B1 Floors233Port.floors233
   ```

   It then writes `final-audit.txt` and checks the axiom whitelist. `await435.py` waits for all required interfaces before that full assembly. These are mechanisms for completing the proof; inspecting them does not establish that full assembly succeeded. The milestone-36 README explicitly distinguishes tested chunks from the full top module and final theorem awaiting all certificates.

5. **The inspected committed audit logs do not establish 231.** `lean435/audit232.log` reports accepted standard-axiom checks for two individual local certificates, `C70123403A663644K24.refuted` and `T012034A34556K12.refuted`. Its filename does not make it a proof of the global 232 bound. `lean435/toy_audit.log` checks generic infrastructure and `upper_254_toy6SC`, and includes intentional rejection controls. Neither log is a completed 563B1/global-231 audit.

6. **The floors port has substantial separate evidence, with integration limits.** `lean435/FLOORS435.md` reports 1,070 accepted modules, 1,897 axiom reports, and the standard three axioms for `Snake9.Floors233Port.floors233`. The handwritten source was committed at `d3a0940d` and its bytes agree with the source hashes in the port/object manifests. Its interface is `DirectionWindow6S.Floors233` and it composes the existing five floor results. This review did not rebuild it or independently hash external Linux objects. The dedicated floors document also records that the 27 shared core/chain modules must be source/object compatible with the final chain, or rebuilt against it; independent kernel rechecking and a fully interface-only final setup were not established there. Older README statements that the floor port is unfinished should therefore be read in light of this newer, more specific evidence, while its integration caveats remain relevant.

## Publication recommendation and remaining evidence

The papers can report: “The contributor branch reports a Lean 4.35 build of a conditional whole-Q9 chain yielding 231; completion of the listed certificate interfaces and the unconditional assembly remains to be verified.” The maintained interval should retain upper endpoint 233. Describing 231 merely as completed with an independent rebuild pending would overstate the inspected evidence.

A responsible numerical update needs a pinned successful full `upper_231_435` assembly, its complete dependency/interface manifest, and the final theorem's axiom audit with the certificate premises discharged. Compatibility of the separately ported floors and chain core must be established. An independent full rebuild remains a separate verification step. This review neither invalidates the reported conditional build nor claims that uninspected external worker output is incomplete.

## SHA-256 pins of decisive source blobs

All hashes below refer to Git blobs at the pinned snapshot, not to local modified copies.

| Path | SHA-256 |
|---|---|
| `lean435/data/auto6sc_563B1.json` | `b2f31eb5f9b09b4c0a08e51b5dad987b9500d342621b208c730bb61dc10adc05` |
| `lean435/data/shards6sc_563B1.sha256` | `8f96aa7eb168a32e1fc1d2c3a531232925eb10905e097d4657ee7d2b4073c989` |
| `milestones/35-231-lean/scripts/gen_lean_chain6sc.py` | `d8e75b0922997be48da9ccf5b97afde746fee162751dec2c5217a9a807b5c361` |
| `work/spectral/stronger/AggregateDirection6SCConditional.lean` | `4b29338285d6aba93f3d7015151cbbf1ee7de9908f0fcb8948c7aead0296539d` |
| `work/final_lean/Snake9.lean` | `025260b9c1533d606a6cfd058aa025d9544d5cd6ccb1f8f5f2143e5657df4740` |
| `lean435/tools/chain435.sh` | `2c483f9d61146b811917a62bb7d014612cbe464a99a38108daca9ca4bd30f3b8` |
| `lean435/tools/assemble435.py` | `79e38c5c7938d3014121d93faf6da1e23ee057fa20c89521d69d331988b18700` |
| `lean435/tools/await435.py` | `7fc6900d099f885c660375fbf3dc9a45196f240c2d46b17cd2dfbf201d00fd0c` |
| `lean435/FLOORS435.md` | `f60711f6bb958929bf6a8d885417124f6283957451ee75821e8554d1c81e2c9e` |
| `lean435/floors/src/Floors233Port.lean` | `c9bec26394a3c2ed029a311694dad61549f6b3a7b9dd892962c8f21439128f25` |
| `lean435/floors/data/OLEAN-MANIFEST.tsv` | `72428000b7fefdee4361f7f6f5aa0d4d89c19e8427aff7552e2a7546861bf3b8` |
| `milestones/36-lean435-port/README.md` | `e0a3a41c604dfe909905f71dc3fc9dbbae4516b1a11fed95fc7cce825753ccd3` |

Only this review file was created. Existing research evidence, manuscript sources, and workers were left unchanged.
