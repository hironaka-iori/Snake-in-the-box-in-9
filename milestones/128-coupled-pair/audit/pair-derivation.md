# Actual justification of the paired counter

Let a snake contain seven successive transitions whose canonical word is
\(0120324\), beginning at index \(r\). Its canonical six-transition prefix is
\(012032\). The previously checked pair theorem gives
\[
\alpha_{r+2}+\alpha_{r+4}\geq 8.
\]
This statement applies to every fitting actual snake window of this shape. It
does not require the six-count total to be at most \(22\).

After translation and permutation of the coordinates, the window vertices are
\[
0,1,3,7,6,14,10,26.
\]
The two relevant centres are \(3\), with incident directions \(1,2\), and
\(6\), with incident directions \(0,3\). At either centre the remaining seven
directions give \(\binom72=21\) opposite-corner occurrences. The checked
actual-snake count transport identifies the number of absent occurrences with
the corresponding \(\alpha\).

Concatenating the two corner lists gives exactly the 42 positions in
`data/pair-counter.json`, in the saved order. Thus
\[
\text{number of selected occurrences}
  +\alpha_{r+2}+\alpha_{r+4}=42,
\qquad
\text{number of selected occurrences}\leq34.
\]
The positions must retain their multiplicity. There are 37 distinct vertices:
\(18,34,66,130,258\) each occur twice, and the other 32 vertices occur once.
Replacing the list with its distinct vertices would change the counter.

## Lean-checked geometric result

`lean/PairLower128.lean` has six checked theorem reports:

- `corner_list_eq` checks the literal 42-vertex list against the two geometric
  corner lists.
- `corner_multiplicities` checks the length, distinct count, and all
  multiplicities.
- `selected_absent_identity` proves the exact count identity for any selection
  predicate.
- `actual_selected_bound` derives the selected-occurrence upper bound from an
  actual snake and a matching coordinate permutation.
- `actual_normalized_bound` constructs such a permutation from the canonical
  shape. No normalization hypothesis remains to be supplied externally.
- `actual_counter_good` derives the existing sequential-counter semantic
  condition from this actual bound. Its remaining encoding premises identify
  the positive literals, their ordered vertex list, and the upper bound 34.
  There is no assumed counting inequality.

The proof uses the checked prefix theorem from round 125, the checked actual
pair theorem from round 121, and the existing count transport and counter
semantics. It introduces no new mathematical definition. The source uses a
local notation for the repeated concrete list.

The successful isolated run took 17.328 seconds. All six axiom reports are
subsets of `propext`, `Classical.choice`, and `Quot.sound`. Source, checker,
dependency, and object hashes remained unchanged during that run. The first
attempt failed because projections from a local notation required
parentheses; its source snapshot and failed log remain saved. That failure
was repaired before the successful check.

| File or evidence | SHA-256 |
|---|---|
| `lean/PairLower128.lean` | `6964a93d036b60a8e427f4459f23462102c9980051bae24b3d9591decaf19bd9` |
| `audit/check_pair_lower.py` | `e24c1c7afd2d1f060ba639df3578bbfce9de3f9a9140a2a5565bbc31a512b333` |
| `build-independent/PairLower128.olean` | `8df4690cbc30703c2978227e829332a4a9f5dea068447d59e4d58439f45ba19e` |
| `logs/pair-lower-1793687781271460700/compiler.log` | `c87f3ccf32da4622363025fd847d424d9cde9b12d8541eb3d27a1508fdd0d64b` |
| `logs/pair-lower-1793687781271460700/record.json` | `14c459d1dc8136f097225a474b6839d0fc9c7d456d2f614b5b62075676ab9996` |

## Concrete counter certificate

The separate generated source `lean/PairClauses128.lean` contains the exact
2863 added clauses and their tags. It preserves counter index 8, the original
primary-variable numbers, all 42 input occurrences, and the new register
variables 7278 through 8705. Its generator independently checks that every
clause variable is either a primary variable or one of these new registers.

The certificate is restricted to the added counter. The eight earlier
counter entries are dummy entries, and their auxiliary variables are absent
from this certificate's meaning map. The checked satisfaction theorem
concerns these 2863 clauses alone. The preceding 101666 clauses, the
conjunction with them, and any complete contradiction remain outside this
certificate's scope.

The concrete source passed its isolated Lean check in 169.813 seconds. Its
four reports establish the following statements:

- `literal_check` verifies the ordered positive-literal map and upper bound
  34, without any axioms.
- `tags_checked` verifies all 2863 concrete tags against their clauses. It
  uses only `propext`.
- `tags_checked_window` shows the checked counter clauses remain checked for
  any window list. It uses only `propext` and `Quot.sound`.
- `actual_pair_clauses` proves that an actual snake with the canonical shape,
  in any matching coordinate frame, satisfies all 2863 added clauses under
  the standard counter assignment. It uses only `propext`,
  `Classical.choice`, and `Quot.sound`. No counting or literal-map premise is
  left unproved in this theorem. The matching frame exists by
  `actual_normalized_bound` in the first module.

This successful check supersedes the earlier pending semantic statements in
the independent review for the added 2863 clauses only. It establishes no
new result for the preceding input clauses or for their conjunction.

Two earlier concrete attempts each reached their 180-second limit with no
captured diagnostics. Their source/checker snapshots, generator bytes, and
generation records remain preserved. Empty captured output does not identify
the stage at which those attempts stopped. The final source uses compressed
empty branches, groups of at most 64 clauses, and noncomputable certificate
data, while retaining kernel checks. These were attempted optimizations;
the evidence supplies no controlled comparison of their individual effects.
The final raw clauses, tags, input order, and variable numbers are unchanged.
All saved dependency and source hashes were rechecked unchanged after the
successful run. No further 600-second retry was needed.

| File or evidence | SHA-256 |
|---|---|
| `lean/PairClauses128.lean` | `3a039fe682b62d6383b644a9c48147b8ee61f6c3704bb624ee208f3fcb999fc2` |
| `audit/check_pair_clauses.py` | `d6439cb11b814930b732a4e371484d99082d78009010c29ef9ef590eb6450801` |
| `audit/generate_pair_clauses.py` | `adb9829815d10f2ae63e2e6604d3b48139d7799c8d70a629fcefc5926348a5c6` |
| `audit/concrete-pair-generation.json` | `10e3ec319f920d43211e0854bac20e42e02b5e1f0255edd569cdb6dcbe3699fd` |
| `build-independent/PairClauses128.olean` | `ed91229d5cda098bdba89213d5cf85769b6ce53dddcbbd1936939fe686949afd` |
| `logs/pair-clauses-1793688604745603200/compiler.log` | `d7b78c777466d86463bb2e5def147d3938a983d82a3815645eba5cd6fb3fb4f3` |
| `logs/pair-clauses-1793688604745603200/record.json` | `c8da35480f8ea53ea5f80b345f0d00c0407dfed22ca34e2cd46f2c18ad983390` |

The generation record retains its status at generation time,
`GENERATED_NOT_YET_LEAN_CHECKED`; the later successful compiler receipt is the
authoritative evidence of the check. That generation record is not rewritten
after compilation because its exact bytes are pinned by the successful
receipt.

The added geometric counter is not asserted to be a consequence obtainable
by RUP from the original CNF alone. It uses the independently proved actual
snake inequality. No result here proves a six-count floor of 23 or a new
global upper bound.
