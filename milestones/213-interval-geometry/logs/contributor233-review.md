# Contributor bound 233: pinned source and saved-audit review

Date: 2026-11-15. Reviewed contributor commit `b0521e1d14fd52c62db4cdeccc356b70a623eb82`, whose direct parent is the audit commit `b65d30ca15441420b8f4538f671e589c2502674f`. All contributor reads used the pinned Git objects. No branch was merged, no compiler or search was run, and no existing source was changed. This is a bounded source/record review, not an independent full rebuild.

## Status conclusion

The contributor now supplies a completed, unconditional 233 theorem and a successful saved final assembly/axiom audit. Describing that contributor result as still having outstanding mathematical certificate premises is stale. The qualification that an independent full rebuild remains pending must remain prominent. This changes the status of the contributor's result; it does not establish local integration or fresh verification of its entire dependency graph.

Suggested manuscript wording:

> The contributor branch contains a completed Lean proof of the unconditional upper bound \(a(9)\le233\), with a saved successful final assembly and axiom audit. Together with the verified 191-edge construction, its stated interval is \(191\le a(9)\le233\). The present review inspected the pinned source and audit records; an independent full rebuild remains pending.

The separate milestone-25 route to 234 remains conditional in its own source history, and is superseded numerically by this completed 233 route. Earlier milestones' conditional statements should retain their historical scope.

## Exact theorem and composition

`work/spectral/stronger/UpperBound233.lean:23–30` states:

```lean
theorem upper_bound_233 {m : Nat} (p : Snake m) : m ≤ 233 :=
  Floors233Port.upper_233_of_certs6SB233
    LocalWindow.allRefuted6SB233 LocalWindow.allRefutedShare6SB233 p

theorem verified_interval_191_233 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 233 := by
  refine ⟨lower_bound, ?_⟩
  rintro m ⟨p⟩
  exact upper_bound_233 p
```

Both are in namespace `Snake9`. No certificate, floor, parity, endpoint or long-length premise remains in the upper theorem. The definition at `work/final_lean/Snake9.lean:6–21` uses vertices `Fin 512`, adjacency by one of nine coordinate flips, an injective sequence indexed by `Fin (m+1)`, and adjacency exactly for consecutive indices. Thus \(m\) counts edges of an induced path in \(Q_9\), without a normalization restriction.

The inspected composition is:

1. `AggregateDirection6SConditional.lean:79–88` combines actual-snake window bounds, share bounds and the checked step inequality under its explicit certificate/floor/table premises.
2. `AggregateDirection6SB233.lean:17–25` supplies the concrete B233 covers and step theorem, leaving only `AllRefuted6SB233`, `AllRefutedShare6SB233` and `Floors233`. Its arithmetic is \(4720m\le1104463\); since \(4720\cdot234=1104480\), the integer upper bound is 233, with margin 17.
3. `Floors233Main.lean:45–52` supplies the five floor results: main's `ShareTransfer152.share16`, the three instantiated catalogue floors for 012031/012304/012314, and `CriticalShare155.share17`. Its resulting theorem retains only the two certificate premises.
4. `work/final_lean/LocalWindowDirUnsat6SB233.lean:39–55,342–365` assembles all 15 new-key chunks, the reused-key source, 19 checked plain-key merges and the H8 merge into `allRefuted6SB233`.
5. `work/final_lean/LocalWindowShareUnsat6SB233.lean:25–516` explicitly assembles 490 share-refutation references into `allRefutedShare6SB233`.
6. `UpperBound233` supplies those two terms and combines the upper theorem with `lower_bound`.

The README reports 2,637 seed certificates and 490 share certificates, 3,127 total. This bounded review did not reconstruct every certificate or enumerate every generated proof dependency; those complete counts are contributor-reported production figures. The 490 direct share references and 19 cloud-build record lines were counted from the pinned sources.

## Saved audit and its limits

`outputs/upper-bound-233-audit-linux.log` identifies Lean 4.19.0, commit `6caaee842e94`, and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. It records 173 chain modules: 172 reused and `UpperBound233` newly compiled in 567 seconds. The final audit exits zero and prints only `propext`, `Classical.choice` and `Quot.sound` for both exact theorem names, followed by `AXIOM AUDIT PASSED`. The total recorded chain time is 761 seconds. The upper-theorem source and audit log have identical bytes at the audit parent commit and the reviewed documentation commit.

`work/spectral/chain_audit.py` explicitly works against an already-built core. Its reuse decision uses modification times, and its final command imports the target and prints the requested axioms, accepting only the three standard axioms above. The actual saved output names the intended two declarations. This supports the recorded final assembly; it is not a fresh verification of every imported object from source.

The contributor documents material verification limits at `milestones/33-233-lean/README.md:313–323,421–444`:

- The audit is Linux-only and incremental; a fresh source-only rebuild has not been performed.
- Certificate sources were deleted after compilation. Regeneration depends on committed core data and generators; no full regeneration was attempted here.
- Nineteen certificates were built on cloud workers and imported after hash and Lean-version checks. Importing an object does not rerun its kernel proof check. An independent object recheck such as `lean4checker` has not been performed.
- Floor-port objects live outside the repository and were imported through an external overlay.
- Reused earlier-key objects include a replay migration with deliberately preserved old modification times. The documentation reports 746 migrated Q/R windows, two earlier R replays and 635 K replays; the old 235/236/237 chains have not been re-audited after that migration. Modification times alone cannot establish exact source/object provenance.
- Two large certificates required a larger stack. This is an execution detail, not an added theorem premise.

This review did not inspect those external objects, rerun the certificates, prove provenance from their current source files, or independently verify every production statistic. These are verification limitations rather than residual hypotheses in `upper_bound_233`.

## SHA-256 of pinned Git blobs

All paths below belong to commit `b0521e1d14fd52c62db4cdeccc356b70a623eb82`.

| Path | SHA-256 |
|---|---|
| `milestones/33-233-lean/README.md` | `69f0fb454810662bc2bc3476396834e291357b503aedda89044ce812583a6389` |
| `work/spectral/stronger/UpperBound233.lean` | `74e745f41e28808e6bcd022a676c99bd2e56660d413257d2b6d83884a94b5e8a` |
| `outputs/upper-bound-233-audit-linux.log` | `56b87aeb853e6b9a16c80130fab8bc1580228e8090d9ffc52eaaeb5696337f8f` |
| `work/spectral/stronger/AggregateDirection6SB233.lean` | `697c30030d8f01304b34fa4f731103ed6c6caa83af513b1b2b8cff53e13b3c35` |
| `work/spectral/stronger/AggregateDirection6SConditional.lean` | `98b78e2300868b52d3e874859d13a4349c2aa1f7a1a9942e62daf743d5f409da` |
| `work/spectral/stronger/Floors233Main.lean` | `468ecf022a55c5011626263adc854bd59df0aaa46e4011340872f185e8b1d4ad` |
| `work/final_lean/LocalWindowDirUnsat6SB233.lean` | `ff3f722a592491f86314be6139133728ce3582f7770b0a05f3e71b028fe0441f` |
| `work/final_lean/LocalWindowShareUnsat6SB233.lean` | `868301d6d339ae3a0051cc9278be8892d69710926dda864cdd4a6ce637693e1d` |
| `work/final_lean/Snake9.lean` | `025260b9c1533d606a6cfd058aa025d9544d5cd6ccb1f8f5f2143e5657df4740` |
| `work/spectral/chain_audit.py` | `c782fee4c166c09a51637a46793cdead59507381f9be9e3dba6b758a5e03da26` |
| `milestones/33-233-lean/certify/data/remotebuild6SB233.jsonl` | `6c51a218660f20e43d86b4eaeb717353888f8901b84d58b50bff5a754c2501ac` |

The long README and generated aggregate files were inspected at their decisive theorem, composition and caveat sections; this report does not claim line-by-line review of the entire contributor repository. The initial broad tree listing exceeded the display limit and was not treated as evidence of complete inspection.
