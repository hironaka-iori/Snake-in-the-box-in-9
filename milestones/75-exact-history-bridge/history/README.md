# Exact prefix-history invariant

Status: **PASS_EXACT_HISTORY**. Lean 4.19.0 checked 22 declarations across two small modules. This closes the history-word invariant, including the meaning of emitted signatures. Numeric graph state and edge coding remain outside this result.

The exact dictionary and rule signatures were copied from `milestones/67-critical-family-charge/data/full-model.json` after checking equality with `milestones/70-proof-supported-share-model/data/enriched-model.json`. The 75 dictionary entries consist of the empty word, 31 words of length one and 43 words of length two. The 58 rule signatures have length three. [source-provenance.json](data/source-provenance.json) records the source hashes and exact copied data; the length histogram is a Python check, while dictionary size, distinctness, prefix closure, maximum length and signature validity are Lean-checked.

## Checked mathematical result

In [HistoryPrefix.lean](lean/HistoryPrefix.lean), `PrefixClosed D` states that deleting the final symbol of every listed word leaves another listed word. The empty word is required separately. `IsLongest D w s` means that `s` is listed, is a suffix of the complete read word `w`, and has maximum length among all listed suffixes.

The essential lemma `candidates_append_iff` proves that, for any listed word `t`, appending a new symbol `a` gives

```
t is a suffix of w ++ [a]  iff  t is a suffix of s ++ [a].
```

For the forward direction, remove the final symbol of `t`. Prefix closure makes the remaining word a listed suffix of `w`; maximality of `s` makes it a suffix of `s`. Restoring the final symbol proves the result. The reverse direction follows by transitivity of suffixes.

Consequently:

- `longest_update_eq`: choosing the longest listed suffix of `longest D w ++ [a]` equals choosing it directly from `w ++ [a]`.
- `run_is_longest` and `run_eq_longest`: iteration from the empty history records the longest listed suffix of the entire word read so far.
- `longest_unique`: two maximum-length suffix words are equal.
- `maximizing_update_eq`: **any** selector satisfying the maximum-length listed-suffix specification yields the same updated word. This is the interface to the Python builder's `max(..., key=length)` scan. The empty fallback is valid because the empty word is listed. Equal-length ties cannot differ as words.
- `emitted_three_is_last_three`: if a three-symbol signature is a suffix of the current history followed by the new symbol, it equals the last three symbols of the complete updated read word.
- `no_emission_first_two`: no three-symbol signature can be emitted when fewer than two symbols have previously been read.

## Exact dictionary instance

[ExactHistory.lean](lean/ExactHistory.lean) contains the copied lists and kernel `decide` checks. `prefixes_nodup` and `prefix_index_unique` establish that an equal selected word has an equal dictionary index; the builder's first-maximum tie convention therefore creates no ambiguity. `signatures_valid` checks every recorded signature has length three and its two-symbol prefix is listed.

`exact_history_invariant`, `exact_history_update`, `exact_signature_sound`, and `exact_no_early_emission` instantiate the generic statements. If `w=[d_0,...,d_(r-1)]` and the new symbol is `d_r`, an emitted signature is exactly `[d_(r-2),d_(r-1),d_r]`; emission is impossible at `r=0,1`. Here each `d_j` denotes an ID of a nine-transition direction window, rather than a single cube-coordinate transition.

The builder reads `hist=prefix[q]++[di]`, advances to a longest listed suffix, and tests signatures against the last three entries of `hist`. All listed histories have length at most two, so a successful three-entry test uses the complete three-entry `hist`. The checked theorem establishes the meaning of this test once the represented history satisfies the invariant.

## Verification and provenance

[proof-audit.json](data/proof-audit.json) contains exact source, object and log SHA256 hashes, the Lean version, all 22 printed axiom lists, and the three direct mathlib source/object hashes. Fresh checks took 4.500 seconds and 6.797 seconds. Axioms are confined to `propext`, `Classical.choice`, and `Quot.sound`; several finite declarations use none. No proof placeholders or native decision tactic occur. Existing mathlib objects were reused without a library rebuild. No contributor proof objects, giant finite transition tables or snake graph objects are imported by these modules.

The two initial runtime attempts encountered a memory threshold and an unsupported runtime configuration option. A subsequent exact-data attempt required unfolding `PrefixClosed` before the kernel decision check. The successful final receipts supersede these diagnostic attempts. Their small failed-record metadata is retained in `logs/` and is not proof evidence.

Reproduce from the repository root using the installed Python runtime with `-X utf8`:

```
python -X utf8 milestones/75-exact-history-bridge/history/scripts/prepare.py
python -X utf8 milestones/75-exact-history-bridge/history/scripts/check.py
python -X utf8 milestones/75-exact-history-bridge/history/scripts/audit.py
```

Only one small Lean process is launched at a time. The check script does not launch a full library build. The larger case7305 proof replay is owned by the parent task and was left unchanged.

## Remaining graph obligation

This result concerns words and their unique dictionary indices. It does not yet define or certify the numeric `q_r` state machine used by the graph arrays. The next assembly step must connect the actual nine-direction ID sequence to its concrete numeric history index, starting at index zero, and prove the builder's selected index satisfies the exposed maximum-suffix specification. Dictionary uniqueness then identifies the result; no exhaustive 75-by-505 replay is needed for the mathematical invariant.

Existing milestone74 source/target shift identities identify adjacent eight-direction state words. They do not supply the 505-entry direction-ID coverage table, the compatible-shape check for each nonempty history, or the full eleven-direction realization set for each three-ID signature. Those coding and coverage steps remain, followed by guard and share dispatch. In particular, one three-ID signature may admit several eleven-direction words, and every compatible variant must be covered by the relevant local theorem. No graph-edge membership, finite potential replay, new numerical bound or optimum claim is established here.
