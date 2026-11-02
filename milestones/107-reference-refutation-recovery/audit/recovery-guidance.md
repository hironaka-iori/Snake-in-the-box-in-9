# Recovery of the selected reference case `d012_a1_1`

This is a source and provenance review. No Lean compiler, SAT solver, LRAT converter, or proof replay was run for this report. The running milestone104 batch was untouched. Paths below are relative to `E:/Snake-in-a-box` unless stated otherwise.

The parent has selected the `Q012A11` route: regenerate an LRAT proof of the exact archived core, then check the recovered semantic and contradiction modules in the current environment. The older `D012A11` route is a smaller alternative with an archived DRUP proof. Both prove the same local exclusion. Neither recovered refutation is claimed as checked here.

## Exact target and composition

Milestone105 `data/source-selection.json` selects union key 0, with directions `[0,1,2]`, symbols `[1,1]`, source catalogue `R4`, source index 0, and root `Q012A11`. Its pinned source revision is `7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b`. The other inspected contributor revision is `74ca83db9c218446211d4f24c5e5a07329fdd847`.

The required proposition is

```lean
Refuted (winOf [0,1,2]) (boundsOf [1,1])
```

Here the window is `[0,1,3,7]`, and the bounds are `[(1,1),(1,1)]`. `LocalWindowModel.lean` defines `Refuted window bounds` as the impossibility of the corresponding `Axioms S E window (centresOf window bounds)`. Its type does not contain the finite CNF radius. Consequently, the radius-three D case and radius-four Q case can discharge this same proposition after their semantic and contradiction proofs have been checked in the target environment.

`LocalWindowTags.lean` supplies `Snake9.LocalWindow.Tags.refuted_of_sat`. It combines a proof that every assignment satisfying the local axioms induces a satisfying CNF assignment with `Unsat` for that exact CNF. Each archived case Sat module provides the former as its `sat` theorem. The regenerated root must supply the latter, for example:

```lean
Snake9.LocalWindow.Q012A11.unsat :
  Unsat Snake9.LocalWindow.Q012A11.cnf
```

A small wrapper can then apply `Tags.refuted_of_sat Q012A11.sat Q012A11.unsat`, unfolding the case window and bounds if needed. This is a proposed composition, not a newly checked theorem in this report. It does not require importing the complete contributor catalogue. Recovering this one key leaves the other exact union refutations unresolved.

## Chosen Q route: regenerate only the pinned core

The radius-four metadata is available at both inspected revisions under both `milestones/10-window-aggregate/data/lean_core_direction_r4/d012_a1_1.json` and `lean_core_direction_r4b/d012_a1_1.json`. Those files have identical bytes. They specify `LocalWindowCnf.Q012A11`, 1,172 retained clauses from a 35,429-clause CNF, and 1,766 variables. Their `core_ids` select the original clauses in order.

The source-compatible procedure is:

1. Recover the exact Q Cnf and Sat sources, the metadata, and `certificates/direction_r4/d012_a1_1.cnf.gz` into an isolated milestone107 directory. Pin their hashes before generation.
2. Decode the natural-number literals in Q's `raw` definition and compare every clause with the full CNF subsequence selected by `core_ids`. The encoding is positive literal $v\mapsto 2v$ and negative literal $-v\mapsto 2v+1$. The parent is performing this comparison. It prevents a regenerated proof of a different core from being attached to the existing semantic theorem.
3. Construct the core-only DIMACS file using these 1,172 clauses. Run CaDiCaL on this file with textual LRAT output. The archived generator uses `-q --lrat --no-binary --seed=1`; a new proof may have different size and still be valid.
4. Trim the LRAT dependency closure of its final empty clause. Preserve only the needed positive RUP hints. The generator's `core_lrat` maps core input ID $h\le1172$ to `core_ids[h-1]`; derived ID $j>1172$ maps to $35429+j-1172$. This puts the proof into the full-CNF input numbering expected by the exporter.
5. Export only `d012_a1_1`, preserving its metadata module name `Q012A11`. Compile the case Cnf and Sat modules, generated proof data/checkpoint modules, contradiction root, and small `Refuted` wrapper sequentially when a compiler slot is available. Preserve source/object/log hashes and the final axiom audit.

The recorded regenerated core proof has 934 lemmas, 38,061 hints, and 8,378 literals. These are provenance figures, not acceptance conditions for a fresh proof. The original generator describes the core LRAT as regenerated and uncommitted. Do not rerun `full_core_ids`, which may select a different core and require a different Sat certificate.

The generator caches an existing `.lrat` together with its `.lrat.json` without independently revalidating every upstream hash. Use a fresh isolated directory or verify all cached inputs explicitly. Successful SAT-solver termination or external LRAT conversion alone does not establish the Lean theorem.

## D alternative: convert the archived DRUP proof

The older metadata is `milestones/10-window-aggregate/data/lean_core_direction/d012_a1_1.json`. It specifies `LocalWindowCnf.D012A11`, 764 core clauses from a 14,200-clause CNF with 1,290 variables. Its recorded LRAT has 670 lemmas, 31,192 hints, and 7,040 literals. The D Cnf and Sat source bytes are identical in the checkout and both inspected revisions.

Both pinned revisions contain `certificates/direction/d012_a1_1.cnf.gz` and `certificates/direction/d012_a1_1.drup.gz`. Therefore this path does not require a new SAT search. The archived `ensure_lrat` procedure invokes drat-trim with `CNF DRUP -L LRAT -t 4000`, requires its verification result, and then exports the selected core proof. The decoded D raw clauses still need to match its pinned `core_ids`, and the resulting Lean modules need checking.

The default binaries `work/keep96/.build/drat-trim.exe` and `milestones/10-window-aggregate/.build/drat-trim` were absent when inspected. Vendored `work/keep96/vendor/drat-trim/drat-trim.c` exists. This is a check of those default locations, not an exhaustive machine-wide binary search. No D conversion or build was launched.

## Generator compatibility

The checkout's `gen_lean_core.py` predates the inspected contributor version. Its `r4` configuration would generate an R-prefixed module without the contributor's reuse mapping. At both pins, `r4` reuses `direction_certificates_r4b.json` and `lean_core_direction_r4b`; `r4b` owns the Q-prefixed source. A broad invocation of the old checkout generator could therefore reconstruct a different module/core. Recover the pinned generator or make a narrowly reviewed single-case driver with the exact Q metadata.

The pinned `gen_lean_lrat.py` also differs from the checkout. It adds explicit literal/hint fuel checks and optional split-database support. Its ordinary `--fast` mode, without `--split`, uses the existing `LratFast` interface. The `LratFast.lean` source is byte-identical at both pins and the checkout. Preserve the ordinary proof protocol unless a separate checker migration is intended. Exporter parameters such as segment size affect performance and proof packaging; they do not replace exact CNF/core correspondence or the kernel checks. Packed literal and slot ranges must remain within the selected encoding width.

## Input hashes

All values are SHA-256. The table records exact inspected bytes; compressed and decompressed files have separate hashes.

| Artifact | SHA-256 |
|---|---|
| Q core metadata, either r4 or r4b path | `6834ccd57be5a7710c74909f12f53d3ef156a700e8b62e80d434c1ecf1b8d037` |
| Q Cnf source at the selected pin | `f6b2884401332b45c31e3f582fb45207960d324305941fb9489811c0fd395cf5` |
| Q Sat source at the selected pin | `bb591690487ae78f35182de954bbf6ff0c6eb56bb7501d5f278ed271b33414fa` |
| Q compressed full CNF | `83db2da9f7095101efaba5df3a1e4a9af3ae63895a31ed3baba59a7e3200526a` |
| Q decompressed full CNF | `f8b4ef6a50ed22fe39b642add1c0bfeeee341465da499f2663cf09f271527e83` |
| D core metadata | `f2024a3fee41188bebc23850b16f4fd56d6c7c594f61180ca953878815282399` |
| D Cnf source | `fa644b7cb5e0a029e06b84edf6448121635ea1abcca1fb5beb7da019179f5358` |
| D Sat source | `aa80c139defeae367a10df2be3788634b947f3b6a1924e852a4f8311fc570137` |
| D compressed full CNF | `d8c4080184db05c819d9b49df295d469cdad0abb08b2242de044677918272a71` |
| D decompressed full CNF | `5e415c28675b87a826bdb879ef0c588c6d0c955d713cff61a6585f99023fa226` |
| D compressed DRUP | `70acc5c8b705e7e5256c0f1fd998ec66c11e95668784ca3820543ab181c61c18` |
| D decompressed DRUP | `8711dc07f3a68aaed2106c256774763960dd3493e82e4581918ff3eeb6dcc035` |
| Pinned `gen_lean_core.py` | `7f4b12eaa27d7734b8e888b31cac6077a7e2cbf8513cb9c31519bc45bf4e3010` |
| Checkout `gen_lean_core.py` | `8cd8deb44476b39932c59d53d74706649356e41803646555bb50f06bf38b4525` |
| Pinned `gen_lean_lrat.py` | `2f4b1339817194163a080468d2e404dd7d14e7c048f8fc90e0a2691b243bf384` |
| Checkout `gen_lean_lrat.py` | `be9ae8f8b280cf9ca3525976bfe297068d72cc683e1605fb7cb6fd2c950c9b8a` |
| `LratFast.lean`, checkout and both pins | `3c28de2b6f8dfca3c451b2cfa3a1865c577935770b7f7128ea69c061e5cf428a` |

## Existing proof environment

The ordered paths in milestone105 `data/environment.json` already provide the following objects. Reuse that order rather than adding legacy builds ahead of it. The directory suffixes below identify existing build roots, not new declarations.

In `milestones/28-direct-share-certificates/build/758bddcc97f84b6fbaa2c693d4931cea`:

| Object | SHA-256 |
|---|---|
| `LocalWindowModel.olean` | `cdff343e0e81adb26337250528ae18a37d4294b6e00cb7ac77cbe223aa6645e9` |
| `LocalWindowTags.olean` | `4817fce74821d3f5c8c2e75e9ab6a996e9c65c0a37eae21d68485dc3849711c0` |
| `LocalWindowTagsPacked.olean` | `b46c9c0d1c107d9a22e5f9eb5f6bd808199044d39abe77ead28ecc0312701384` |
| `LratCheck.olean` | `32d59da80d0c9017b0ca0d64b5bd782f5c44d4b960e2a2e08216a3f81eea119b` |
| `LratFast.olean` | `a62a30cc4872321c4a08585ce59105a2d3aa4b8bc15ea14bf13253fcde86d05b` |

`LocalWindowDirModel.olean` is in `milestones/32-seven-count-four-screen/build/cc4a6ed007924637afe87021c13a85ca`, hash `c2b39c7a3013f42ac09d6737542567c2e6571553d687f98a7b24f457c3b067af`.

The six D/Q case-specific Cnf, Sat, and Unsat objects were absent from all milestone105 environment paths inspected. The support objects therefore avoid a broad closure rebuild, while case-specific checking remains necessary. This report establishes an actionable reconstruction path and the exact proof boundary. It establishes no recovered closed refutation, complete reference union, or new snake bound.

## Additional exact alternatives in the older catalogues

After the preceding investigation, the parent reported successful Q recovery: 19 isolated modules, 14 axiom audits, the exact first-key refutation, and the reduction of the full union requirement to its remaining 1,377-key tail. The additional comparison below is read-only source evidence; it does not claim that the alternative D roots have been replayed.

At pin `7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b`, exact ordered pairs of direction and symbol lists give:

| Older catalogue | Catalogue keys | Exact keys in the 1,378-key union | Matching core metadata |
|---|---:|---:|---:|
| `LocalWindowDirKeys`, direction | 145 | 90 | 90 |
| `LocalWindowDirKeys5`, direction5 | 175 | 134 | 134 |
| Distinct union of both older catalogues | 201 | 143 | 143 |

The older catalogues share 119 keys, of which 81 occur in the target union. Thus the distinct overlap is $90+134-81=143$, comprising 9 direction-only matches, 53 direction5-only matches, and 81 shared matches. Key 0 is included, leaving **142 additional union keys with exact older D alternatives**. The other 1,235 union keys have no exact match in these two older lists. No reversal, canonicalization, monotonicity, or implication between different keys was used to enlarge the count.

All 320 catalogue-specific metadata records were present. Their `dirs`, `syms`, module names, reconstructed XOR windows, and bounds agree with their catalogue keys; symbol 6 was checked as `[6,21]`. Core clause indices were unique and within the stated full-CNF range. The corresponding Sat wrappers apply `Tags.refuted_of_sat` to every expected D root exactly once, and the Unsat wrappers refer to those same expected roots exactly once. This identifies the same advertised `Refuted (winOf dirs) (boundsOf syms)` targets. It remains dependent on successful checking of the individual root proofs.

For the 143 distinct matching D roots, the pin contains all 143 Cnf sources, all 143 Sat sources, and all 143 full-CNF archives in `certificates/direction`. Of these, 114 also have an archived DRUP file there. No corresponding `LocalWindowUnsat.D...` root source is committed. Presence of a DRUP file is only an availability result; it does not establish that conversion reproduces the currently selected core. Core-only regeneration using the pinned metadata is the common route for all 143, while DRUP conversion remains an option after correspondence checks.

The smallest **recorded hint count among these alternatives** belongs to union index 472:

```text
directions: [0,1,2,3,0,4]
symbols:    [2,2,6,2,3]
root:       D012304A22623
metadata:   data/lean_core_direction5/d012304_a2_2_6-21_2_3.json
core:       120 clauses
recorded proof: 75 lemmas, 426 hints, 135 lemma literals
```

This is the next useful single-case recovery choice: it is an additional union key, has a small recorded core proof, and exercises the interval meaning of symbol 6. Its 120 decoded Lean raw clauses were independently compared with the exact subsequence selected by `core_ids` from the archived 29,055-clause CNF; all matched. The largest variable in this core is 2,374, compared with 2,773 declared for the full CNF. Any regenerated proof must still satisfy the exporter's literal and slot bounds. Recorded proof size does not guarantee regeneration time or a particular new proof size. No solver, conversion, or compilation was performed for this candidate.

Comparison input hashes:

| Artifact | SHA-256 |
|---|---|
| Milestone85 `data/reference-union.json` | `dea948631bbccd4c81a1b590dfeeb7f606bd44fc664861f7667b6d041e267289` |
| `LocalWindowDirKeys.lean` | `320dcca95131e8a6f17ecd877347c2bca4711be676fc4e2e5603bd6605150217` |
| `LocalWindowDirSat.lean` | `1fffc3e50da61d397139e01c9a837c42c29dea8732c2e6db167d6a405ccc2ed7` |
| `LocalWindowDirUnsat.lean` | `ddf71168840c58f088750bc1c2cf3381f8e9515060f9755582a1317940207ea8` |
| `LocalWindowDirKeys5.lean` | `839913db6c1a5c18d9fb7c734fa90da0f51793cc1e0be46db4db43fb38bbc0d3` |
| `LocalWindowDirSat5.lean` | `e68e9447df29adec34aa3c74574cdf4585e05b6e6702eb62ace4eed4c95acbd4` |
| `LocalWindowDirUnsat5.lean` | `be490ccf81b9932bb3c888f1be1efb5635ca9dc94115b098ca06e6f5b2529a13` |
| Candidate metadata | `a624e1df1a2956dd08c049c4f340e8b395c4c6b6e2015d8826eda05c4d971e8d` |
| Candidate Cnf source | `21a9fc070053b485acbd5fa92b12b6d0809cf34ee49ab8d4e96b8341aed04372` |
| Candidate Sat source | `99708d59913a518f14da6186710ffcf02ba18df9be655357bb20974ee4a0b2ee` |
| Candidate compressed CNF | `41bc1f5303637df2d80cbe28d1da58dfaaa63f568e64001fbdc4c77e7ed5e7f2` |
| Candidate decompressed CNF | `dfb76457875b6483fd38e28f1df6ac93bd6b266982ab6484c83e2209a826e634` |

For an additional aggregate provenance check, sort the 320 metadata Git paths lexicographically and concatenate `path`, one space, the lowercase SHA-256 of that file's exact bytes, and a newline for each path. The SHA-256 of this UTF-8 concatenation is `8dc8dfe5b80754fdad2061ac8c9ed188cc382a92e69b09ee71e856265234b72d`. Only this report was changed; no certificate or existing research source was modified.
