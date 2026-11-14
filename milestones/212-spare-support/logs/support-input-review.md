# Spare-support input and root review

Date: 2026-11-14. Result: all inspected input, model and root-preservation equalities agree. Only saved files were read and this report written. No search, compiler, Lean run, software test or process operation was performed; the current mutable search state was not inspected.

The new `model.json` and `permutations.json` are byte-identical to original round-207 case 22. Its model hash agrees with the original six-coordinate summary, the round-209 census, the support declaration and the preparation receipt. The model has 78 variables, retained coordinates `[0,6]`, six free coordinates, 2,600 binary relations, 120 nogoods and 120 permutations.

The original relation/nogood/permutation input was independently serialized in its original order: 3,409,996 bytes. The new tail preserves this complete prefix and appends exactly 862 bytes, comprising 298 integers. Independently parsing the suffix in the C parser's field order reconstructs exactly two declared families, all clique and outside indices, each partner count/list and both word masks. There are no trailing tokens or unaccounted fields. Reconstructing the complete tail gives exactly the saved 3,410,858 bytes across 2,867 lines.

The families equal the original census records, including order and partner lists. Each partitions the 39 model variables of its parity into distinct, disjoint clique and outside lists; every relevant root domain is nonempty and lies in the corresponding 32-word alphabet. Partner keys exactly cover the outside variables, with distinct partners contained in the clique. All required inequalities were independently reread from the original binary tables:

| Family | Clique | Outside | Spare words | Required unequal pairs | Checked equality entries |
|---|---:|---:|---:|---:|---:|
| Even | 30 | 9 | 2 | 660 | 21,120 |
| Odd | 26 | 13 | 6 | 631 | 20,192 |

All 41,312 entries forbid equality. The appended support rules therefore use the exact concrete assumptions established in `logs/support-engine-review.md`.

The fixed initial state contains exactly one region, ID 0, with all 78 original root domains unchanged. It has zero jobs, nodes and seconds, an empty receipt list, next ID 1, and status OPEN. Independently rebuilding that object and its serialization reproduces the initial-state bytes and receipt hash. No branch is removed or inherited from the earlier nonresumable limited run: this is a complete restart of the same source-model root. All seven engine pins and four model pins match their actual files and the preparation receipt.

`prepare_case.py` was inspected without execution. It refuses an existing destination, verifies the source model, checks the family membership and binary inequalities before writing, copies the model/permutations exactly, and appends the support declaration after the complete original input. The pinned generic proof receipt agrees with the preparation record; this audit makes no independent compiler claim. Native search coverage, future state transitions and the full snake-to-model interpretation remain outside this input review.

## SHA-256 pins

Paths are relative to `E:/Snake-in-a-box/milestones/212-spare-support/` unless marked otherwise.

| Artifact | SHA-256 |
|---|---|
| `scripts/prepare_case.py` | `697244ce9392aebc7f2a5e1d3ba119e92347affeefb246e27d2f3b00d4c12ba5` |
| `data/root-preparation.json` | `1f121aecc2df8a7d131057ac93a6b62fdfddf19d75dd6ae608f78eac5a32a7f8` |
| `data/case-22/initial-state.json` | `e9d52f433edd04b330bb7f08cae46a865b231c7d599a25dae005b96dae103334` |
| `data/case-22/input-tail.txt` | `a6d93cdaac4436edd25781756128a569e71cd61ee350fd4745d58eed3bbb9689` |
| `data/case-22/support-constraints.json` | `0362c97affd2b4b19405f2a05747327a703b55459b6f1cb3d7bc455c72bce040` |
| `data/case-22/model.json` | `1a4d81c600d104347a501cfc9bf82db91a3aa04a6ebfd3ea20fcb1ca283aa95b` |
| `data/case-22/permutations.json` | `7e4e3dde90085bc5365ae29d2af69af62281fe52d69ea73482e4ef257a0abb93` |
| `data/SpareSupport212-audit.json` | `6477a892009008091cc7525162ea3cdd7c4ca9a27d81a2fcfc4f58d2e1bbe380` |
| Round 207 `data/six-coordinate-summary.json` | `a8c1435ff5dff39711ab2269b0fd24e1f6e386830dad887a58cbba7cfe41a8be` |
