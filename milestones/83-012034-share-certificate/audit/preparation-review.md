# Independent preparation review: case7302

Reviewed 2 November 2026. No mismatch was found between the selected 012034 share20 target, native certificate, compact formula, generated clause literals, and proposed geometry/reversal statements. This is a preparation and source review. No completed local theorem receipt existed at inspection, and no Lean or solver job was started by the reviewer.

## Intended statement

The generated `Share7302/Geometry.lean` states that, for any snake p in Q9 containing six consecutive directions

\[
(a,b,c,a,d,e),
\]

where a,b,c,d,e are distinct valid coordinate names and r+6 <= m, the five internal centres satisfy

\[
20\le\sum_{i=0}^{4}\operatorname{coreShare}_{12}(p,r+i+1).
\]

The only intended caller assumptions are the snake, valid distinct coordinate names, the fitting window, and these six directions. There is no prescribed singleton-count pattern. The five internal singleton bounds 0 <= alpha <= 21 are derived by `coreAlpha_le_21`; the positions r+1,...,r+5 are strictly internal under r+6 <= m. This bound applies even when the window begins or ends at a snake endpoint.

The certificate has resolution12 and cap19. The shared bridge converts refutation of share sum at most19 into integer lower bound20. The statement concerns the sum of integer shares at resolution12; it is not a claim that the window forces twenty distinct empty squares.

The proposed reversed statement uses the word (e,d,a,c,b,a), exactly the reversal of (a,b,c,a,d,e). It applies the forward statement to `revSnake p` at m-r-6 and reverses the five-centre share sum. No extra coordinate, count, or endpoint assumption appears.

## Selected target and native input

The current `data/case.json` contains case7302, shape index2, directions `[0,1,2,0,3,4]`, and required share20. Its copied native metadata exactly matches the current `pysat2-cap19-certificate.json`, including its recorded byte hash. The native metadata has cap19, five bounds `(0,21)`, and an empty cycle-cut list.

The native verifier log `72-four-count-proof-closure/critical-current/logs/pysat2-cap19-verify.log` ends with `s VERIFIED`. It records 15,446 retained core clauses from 99,818 clauses, with 298,203 core lemmas and 31,410,188 resolution steps. This is the existing native verification record; no verifier was rerun by this review. Its success is separate from the pending Lean semantic interpretation and replay.

The generated canonical vertex sequence is

\[
(0,1,3,7,6,14,30).
\]

It was independently reconstructed by coordinate flips. Its seven vertices are distinct, consecutive vertices have Hamming distance one, and every nonconsecutive pair has distance other than one. The forward and reversed directions therefore describe the intended induced local path shape.

## Original, compact, and generated clauses

The actual full-CNF and extracted-core hashes match both native metadata and the generated mapping receipt. Independently of the preparation script, the reviewer:

1. Read all 99,818 native clauses and the 15,446 original core clauses.
2. Applied every recorded original-clause index and checked equality with the corresponding extracted core clause, allowing the intended within-clause literal reordering.
3. Applied the recorded variable renaming and compared all resulting clauses with `certificates/share7302.cnf`.
4. Parsed every generated Lean `rawN` clause chunk and compared the flattened list with the signed-literal encoding of that compact CNF.
5. Checked that the active original variables map bijectively onto identifiers1,...,6238 and that the compact formula uses no larger identifier.

All checks passed. The mapping contains 6,238 active variables and 6,831 semantic variables; the additional semantic names support counter/totalizer interpretation and are not additional compact clauses. The 15,446 clauses are split into 121 semantic shards.

`prepare_lean.py` constructs `TaggedShare` with exactly the selected directions, broad bounds, and cap19, then requires its full clause list to equal the native CNF. It adds only recorded cycle cuts after checking their type; this case records none. The core selection preserves original clause ordering for the tag checker. No extra local-count or endpoint condition is inserted by this preparation source.

This comparison checks clause identity and provenance. Correctness of their interpretation as consequences of actual-snake geometry still depends on the pending semantic Lean checks and the inherited soundness support.

## Geometry and final audit boundaries

The geometry proof's coordinate permutation matches the repeated first direction and the other four distinct directions exactly. The copied `LocalWindowShareBridge.lean` matches its pinned source hash `8b2d06a67664f7d9ded4d0b3422e8cf73c151caed2a0cc08772ec74cf7d59ca8`. Its `refuted_share_bridge` needs the checked refutation, canonical window, matching directions, and count bounds. Those are precisely the intended obligations supplied by the generated geometry wrapper.

`audit_share.py` requires a successful source-matched geometry record before producing `PASS_LOCAL_SHARE_THEOREM`. It then checks every generated Lean source against successful records, dependency source hashes, existing compiled objects, logs, and printed axiom lists. Because the reversal source is present, it too must have a successful matching record. The audit also reconstructs the native clause list, original-to-compact mapping, Lean literals, and requires successful export simulation.

This final audit has not yet passed for case7302 at this review point. Generated geometry and reversal source text must not be described as checked theorems. Native DRAT verification, semantic shard progress, completed LRAT replay, arbitrary-snake wrappers, and the final source/axiom audit remain separate gates. The inherited support is reused rather than rebuilt from a clean environment.

The case record's `proved_cnf_share: 20` is confined to its native-CNF evidence. Its explicit pending scope correctly prevents interpreting that field as a completed universal-snake result.

## Conclusion

The prepared target is the intended count-free share20 statement for 012034, and the native-to-generated formula correspondence is consistent. No silently added geometric/count assumption or off-by-one error was found in the reviewed sources. The strongest current conclusion is verified preparation plus the existing native certificate. The universal local theorem, any resulting complete-graph mean improvement, and a new global upper bound remain unproved by this review.

## Reviewed fingerprints

- `cases/case7302/data/case.json`: `7184aa0a1f61deb0d06d6ce5b67f96049a68e6ab8499636e66239c5bc7907f89`.
- `cases/case7302/data/share7302.json`: `31a63a0954b61f273888602b1520e334df2be452ebe94bc2d58f1d46b33a8920`.
- `cases/case7302/lean/Share7302/Geometry.lean`: `0e0737f6478b7a85e021167b3e0d84a744efd7e4d45dd73f3cd0f73b5f5d1cee`.
- `cases/case7302/lean/Share7302/Reversal.lean`: `c040d924011c675760dc20d45e9e1376fad0559caeb666865bdcdc548aa916b1`.
- `cases/case7302/scripts/prepare_lean.py`: `276888d8d56049c050fa1b4561fe0252c929f2c2817d62cb1a6ffdab03256642`.
- `cases/case7302/scripts/audit_share.py`: `b79c1d15d1f828175b29b773134cfb8bb6df9838fb2c7c17b3323bf8929e92e7`.
