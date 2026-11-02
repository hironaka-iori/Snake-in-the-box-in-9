# Semantics of a sorted count-sum counter

`lean/SumCountSemantics112.lean` passed Lean 4.19.0 in 1.578 seconds, with three printed axiom reports. It introduces no definitions or types. It proves generic list semantics and counter soundness under explicit hypotheses; it proves no concrete local count inequality or actual-snake exclusion.

The existing `LocalWindowTags` lemmas `countP_corners_abs`, `base_negP`, `ctr_bound`, `ctr_lit_ok`, and `ctrOK_getD` were read before implementation and reused directly. The module imports the checked `CounterSound111` and uses its generic CNF soundness theorem. It does not duplicate counter assignments or clause semantics.

## Checked interface

All statements are in namespace `Snake9.SumCountSemantics112`.

`countP_permuted_corners` takes selection predicates $S,E$, metadata $M$, a literal list, and a list of selected centres. Its hypotheses require that every literal is a negative primary literal and that the list of mapped vertices is a permutation of the concatenated corner lists. It proves that the number of true literals equals the sum of `absentCorners` over the supplied centre list.

The proof first applies `base_negP`, then permutation invariance of `List.countP`, then `countP_corners_abs` to each concatenated block. It uses lists throughout. Repeated vertex occurrences, repeated literals, and even repeated centres retain their multiplicity. No distinctness assumption is introduced. In particular, the 84 occurrences of the milestone 111 sorted counter must be matched to all 84 concatenated corner occurrences, rather than to their 77 distinct vertices.

`sound_append` takes an ordinary counter list `cs` and one counter `extra`. It assumes:

- the exact clause-tag check `ckAll` for `cs ++ [extra]` succeeds;
- all ordinary counters pass `ctrOK` for the ordinary window and bounds;
- every literal of the extra counter passes the existing base-literal validity test;
- the number of true literals of the extra counter is at most its stored cap;
- the existing window axioms hold.

It concludes that the existing assignment `tau` for this appended list satisfies the decoded CNF. For old indices, `ctrOK_getD`, `ctr_lit_ok`, and `ctr_bound` supply the two hypotheses required by `CounterSound111.sound`. At index `cs.length`, the explicit extra-counter hypotheses apply. Larger indices use the unchanged default counter with an empty list and cap 2; both obligations are discharged. Thus the adapter retains out-of-range semantics rather than silently assuming every counter reference is in range.

The extra counter's existing `kind` field is not used to infer its bound. Its bound is supplied explicitly, as required by `CounterSound111`. This permits a joint sum without modifying the existing counter type or claiming that the old single-centre `ctrOK` test accepts it.

`sound_append_sum` combines these results. It replaces the extra literal-count bound by the explicit bound

$$
\sum_{c\ \text{in the selected centre list}}
\mathrm{absentCorners}(S,c)\le \mathrm{extra.k},
$$

and requires the negative-primary and permutation hypotheses for `extra.lits`. It retains the explicit base-literal hypothesis. The selected centre list is supplied by the caller; the theorem does not claim it equals any particular positions of the window. That concrete identification and any subsequent actual-snake interpretation remain necessary.

## Check and repair record

There were two source repairs and two Lean invocations. The first invocation failed because the count-congruence API required an equivalence of Boolean truth statements, the induction retained a dependent permutation hypothesis, and the inherited environment did not expose optional `getD` append lemmas. Its exact source, checker, compiler output, and failure record remain under run `1793658973137400700`.

The first repair corrected the Boolean and induction arguments and attempted an optional Mathlib list import. The dependency check then stopped before launching Lean because `Mathlib/Data/List/GetD.olean` was unavailable. That intermediate source and checker are preserved under run `1793658992021069600`, with a separate preflight record. No historical dependency was compiled or changed.

The second repair removed that import and used the already imported core `getElem?` append and default lemmas. Run `1793659023061976800` passed. The permutation theorem reports only `propext` and `Quot.sound`; both soundness adapters additionally report `Classical.choice`. The successful source contains no `sorry`, `admit`, or `native_decide`. The failed log's placeholder axiom reports remain failed evidence and are not included in the successful receipt.

The checker uses the audited milestone 111 import paths, prepended by the fresh `build-sum-semantics` directory. It checks the exact `CounterSound111` receipt, source, immutable snapshot, object, and log; the resolved `LocalWindowTags` object is compared with the hash in that inherited receipt. It also pins the inspected Tags source, environment receipts, package manifest, and Lean executables. This reuses the prior checked import environment; it does not claim a clean rebuild of the full dependency closure.

At successful launch, the memory gate observed one other Lean process, milestone 104 PID 24860, with 183,488,512 bytes of private memory. The gate requires at most one other compiler and less than 8 GiB aggregate private memory. The checker used a 120-second timeout and no unsupported memory-limit option. The compiler slot is released. The accepted `SumBudget112` files and milestone 104 remained unchanged.

## Evidence pins

Paths are relative to milestone 112.

| Artifact | SHA-256 |
|---|---|
|`lean/SumCountSemantics112.lean`|`23b816a0f54dce1fd6fb502c6b366bfac58ac3bf86cdff4c874d7105e848f5c7`|
|`build-sum-semantics/SumCountSemantics112.olean`|`00ddd59e5e5f6771e6365ec25a8c4d17e5a902464e290db682c9079a3ae9ceb8`|
|`scripts/check_sum_semantics.py`|`30c3a899cfabffdf2570925f876e1650174b26eff14102062313dc0af5aec6f7`|
|`logs/SumCountSemantics112-1793659023061976800.log`|`5d57f8e82396f59c1514b4cb7312a4a8d087d405720ce77a8777d09a4bf08a5b`|
|`data/SumCountSemantics112-audit.json`|`0c887390bdfddf201fd4a359026ad50f5bf3ad84c67ee4e79e4eb1d8a070cd2d`|
|`logs/SumCountSemantics112-1793658992021069600-preflight.json`|`eef1e4bbd256e9edbd57a2c523fe692b9d31d92d17b4dade78c131b2a34a7def`|

Concrete sorted metadata, finite permutation and clause checks, the contradiction certificate, and transfer to actual snakes are still required before a local sum hypothesis becomes a theorem about snakes.
