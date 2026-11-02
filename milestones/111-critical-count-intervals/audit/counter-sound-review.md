# General counter soundness

`lean/CounterSound111.lean` passed the isolated Lean checker in 2.875 seconds, with six standard-axiom reports. The module introduces six theorems and no definitions, inductive types or new axioms. It proves generic clause and CNF soundness; it does not itself prove the proposed outer-count inequality or any actual-snake exclusion.

## Interface

The final theorem is `Snake9.CounterSound111.sound`:

```lean
theorem sound (M : MT) (cs : List Ctr) (w : List Nat)
    (b : List (Nat × Nat)) (tags : List Tag) (raw : List (List Nat))
    (h : ckAll M cs w tags raw = true) (S E : Nat → Bool)
    (hbase : ∀ c i, i < (cs.getD c dfltCtr).lits.length →
      baseOK M ((cs.getD c dfltCtr).lits.getD i 0) = true)
    (hb : ∀ c, (cs.getD c dfltCtr).lits.countP (lv (base S E M)) ≤
      (cs.getD c dfltCtr).k)
    (ax : Axioms S E w (centresOf w b)) :
    cnfTrue (tau S E M cs) (raw.map (·.map decodeLit)) = true
```

The supplied `hbase` requires every in-range counter literal to denote a primary vertex or endpoint flag. It provides the equality between the base assignment and the full assignment on counter inputs. The supplied `hb` requires the true-literal count of every counter, with multiplicity, to satisfy its bound under this particular `S,E` assignment. Out-of-range counter indices retain the existing `dfltCtr` behavior. There is no assumption that counter input lists are duplicate-free.

The theorem takes the existing clause checker `ckAll`, rather than the stronger `checkAll` that also insists on the original `Ctr.kind` justification. Consequently an existing `Ctr` can represent a sum-of-counts counter if the caller independently proves its input-literal validity and numerical bound. No counter meaning is accepted merely because of its metadata label.

## Proof adaptation

The source adapts `sound_first`, `sound_step` and `sound_over` from `work/final_lean/LocalWindowTags.lean`. In the first two cases, the original derivation of literal validity from `ctrOK` is replaced by the explicit `hbase` premise. The overflow case additionally replaces the original `ctr_bound` call by `hb`. The prefix-count, literal-negation, register and arithmetic arguments are unchanged in substance.

All geometry clause cases, including cycle cuts, reuse the imported soundness lemmas. The zero-register and monotone-register cases also reuse the original lemmas directly. The new `sound_clause` dispatches these cases; `sound_all` follows the existing recursive list proof; `sound` converts clause satisfaction to CNF satisfaction. Every original clause guard remains in force, including literal indices, register identities and the positive bound required by `ckOver`.

The next concrete application must still supply a checked `ckAll` equation, prove `hbase` for its data, and prove `hb` for every counter. For a joint counter, identifying its `countP` value with the intended sum of singleton counts is a separate necessary proof. Combining this helper with a checked UNSAT certificate requires those concrete obligations; no such conclusion is implicit here.

## Check and provenance

The first checker invocation stopped before starting Lean because the Python process used Windows cp932 decoding for the UTF-8 source. Its record is preserved as `logs/check-run-1793656289623676000.json`. The unchanged source then passed with `PYTHONUTF8=1`; no checker or dependency file was edited. The successful run is `logs/check-run-1793656300472981100.json` and the receipt is `data/CounterSound111-audit.json`.

All six printed statements, `sound_first`, `sound_step`, `sound_over`, `sound_clause`, `sound_all` and `sound`, depend only on `propext`, `Classical.choice` and `Quot.sound`. The checker verified absence of `sorry`, `admit` and `native_decide`. The receipt's shared scope text mentions actual-snake exclusions generically; the exact scope of this particular module is the conditional soundness interface above.

The direct imported `LocalWindowTags.olean` was resolved from `milestones/28-direct-share-certificates/build/758bddcc97f84b6fbaa2c693d4931cea/LocalWindowTags.olean` and pinned to `4817fce74821d3f5c8c2e75e9ab6a996e9c65c0a37eae21d68485dc3849711c0`. The inspected adaptation source `work/final_lean/LocalWindowTags.lean` has SHA256 `1e9aad3e4c99acf4fa01b00dcc65330a8d633826079a3d0955716ccb0f36ec71`. The checker also pins the inherited environment and receipts; this task did not rebuild their dependency closure.

| Artifact | SHA256 |
| --- | --- |
|`lean/CounterSound111.lean`|`1401c38d80c4e39c8ee43928af85394c3863f670a0f308cccff09aefabe9b2c4`|
|`build-isolated/CounterSound111.olean`|`35db8221a64f6d5af3f067617dfd90869696aaec97578495f2f9f957d96beb27`|
|`logs/CounterSound111-1793656300472981100.log`|`d5e98c5a0735b3508788b189a8c43bd0c4d0077d8e53c153e1d704ed317e509f`|
|`data/CounterSound111-audit.json`|`7c40150800a9b91e71e3d786e241f08acdd89269e0ba16ef45c42dfef2752b93`|

The compiler session is terminal. No additional compiler was started after this successful check, and milestone104 was untouched.
