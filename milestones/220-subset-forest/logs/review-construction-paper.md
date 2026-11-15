# Round 220 review of the construction and historical half

## Scope and evidence

Read every line 4140–10979 inclusive of `data/before-snake9_research.tex`, including the complete construction discussion, verification section, historical appendices, printed witness data, catalogues and bibliography. This is 6840 source lines. Read the ranges 4140–4640, 4641–5140, 5141–5640, 5641–6140, 6141–6640, 6641–7140, 7141–7640, 7641–8140, 8141–8640, 8641–8940, 8941–9240, 9241–9540, 9541–9940, 9941–10240, 10241–10600 and 10601–10979. Output truncations were repaired by rereading 8420–8444 and 9700–9812. No assigned passage was left unread.

Also read all 620 lines of the companion frontier explanation; its findings are in `logs/review-frontier.md`. The manuscript's first 4139 lines are outside this review assignment. References to results there were examined for their use and stated premises, rather than independently verified against those earlier proofs.

This is a complete source review of the assigned text, with direct inspection of its written deductions. It is not a fresh Lean rebuild, a replay of archived certificates, a rerun of native enumerations, an independent check of every printed numerical witness, a verification of external citation contents, or a PDF layout review. No software tests, solver jobs or heavy computations were run. The review leaves the maintained interval at \(191\le a(9)\le233\), with the contributor theorem and saved audit qualification stated at lines 7401–7408. It does not remove the pending independent full rebuild.

## Corrections recommended before publication

1. **Undefined summand in the five-window proof, line 8485.** The displayed equality uses `\sum_i L_i`, although the subsection defines the window contribution as \(H_i\) at 8466–8468 and bounds \(\sum_i H_i\) immediately above at 8483. Replace only `L_i` with `H_i` in that equality. The argument then agrees with its definitions; no numerical constant changes.

2. **The verification summary stops ten rounds before the current source, lines 7541–7554.** It ends with the round-209 six-coordinate status and a sentence about the round-210 review, although the main text includes rounds 211–219. Replace that final construction-status paragraph with a current summary retaining the distinction between native completion of one retained-coordinate pair, the 27 unresolved pairs, checked generic and source-specific pruning deductions, unresolved direct 93-edge partner queries, and the round-219 exact fractional assignments of total weight 94 satisfying every cycle inequality. State that those assignments are not paths. Preserve the source-specific and full-rebuild limitations. A round-220 result, if obtained separately, must be incorporated only after its outcome is known.

3. **Fractional feasibility is phrased as selecting a number of vertices, lines 7371–7373.** The proposition is explicitly about a continuous formulation, but “admits a selection of exactly 94 vertices” can be detached from that qualification and read as an integral witness. Use “admits a fractional assignment with total selection weight exactly 94, satisfying every simple-cycle occupancy inequality.” Keep `prop:cycle-relaxation219`, the convex-mixture proof and the explicit no-snake conclusion. The proof's weight \(92/(q-2)\) is the correct solution of \(\lambda q+(1-\lambda)2=94\).

4. **An already completed search is still announced, lines 7225–7228.** The degree-and-cycle search described in the future tense is executed in the immediately following subsection, at 7233–7279. Replace the sentence with a backward or present cross-reference to `sec:partner218`; retain the two UNKNOWN outcomes and the absence of a demonstrated runtime advantage. Likewise, 7390–7398 is the correct pre-round-220 proposal and must be replaced by the actual round-220 outcome if this review accompanies that calculation.

5. **Clarify the endpoint indicator convention, lines 7287–7309.** Here \(e_u\) denotes the free endpoint, while the fixed root is handled separately. State \(e_u=0\) for every even vertex, including the root, or define \(e_u\) only for odd vertices and extend it by zero. The current phrase “at even vertices other than the root” leaves the root's indicator unspecified. Its omission does not alter the displayed nonroot equations, but the definition should determine the entire model unambiguously.

## Structure and current-versus-historical status

- The construction sequence 4140–7398 contains substantial general mathematics, but its main line is interrupted repeatedly by timings, partial-search counts and successively superseded bounds. Retain the general joining criteria, replacement identities, symmetry/history results and current restricted conclusions in the main argument. Move detailed per-round progress to a construction-record appendix while preserving every existing theorem and reference label. For example, the omission progression at 4487–4507, 4607–4629 and 4695–4705 can be summarized by its strongest currently stated restriction, at least eight omissions and ten additions for the specified fixed-endpoint problem, with the earlier stages retained as historical evidence.

- The joint-support and matching material at 6752–7198 mixes theorems with implementation history. A single latest-status table can distinguish the four saved open cases, the sole exhausted six-coordinate case, and the remaining initially limited cases. Put stage-specific region counts and raw operation counters beside their archived round, rather than repeating them as successive “current” statuses. These are descriptions of different cutoffs, not contradictory mathematical results.

- Several older future statements remain inside the main construction narrative: 4384–4387 announces the replacement investigated immediately afterward; 4713–4728 describes a “possible next search”; 5480–5483 announces root cases later reported at 5575–5580; 5970–5973, 6085–6086 and 6239–6240 identify genuinely unresolved scopes. Change only the first category to historical wording or cross-references. Do not turn genuinely unresolved scopes into completed exclusions.

- Historical graph obstructions at 7557–8583 are generally labelled correctly and keep their graph, weight and boundary premises. Preserve this separation. Their 234/235 comparison targets are numerically superseded by the completed contributor 233 result; they remain useful method-specific statements. Future-language examples at 7665–7668, 7774–7775, 8221–8223 and 8527 should be anchored to the historical calculation rather than presented as the present route to a stronger global bound.

- The historical theorem statements at 8568–8583, 8646–8655, 8672–8715, 8785–8907 and 9161–9177 repeat boxed weaker intervals. Their mathematical implications remain valid. One appendix-level statement that these are successive historical bounds would reduce the chance that a reader mistakes a prominent boxed interval for the maintained result. Preserve theorem labels and numerical deductions.

- The separate verification section 7400–7554 repeats a long certificate history already carried by individual proofs and bibliography entries. A dependency table would be easier to maintain: theorem or model, geometric coverage, certificate completion, finite-data audit, full rebuild status. Keep the contributor B233 chain independent of the retained conditional-share calculations; completing one chain does not discharge the other chain's premises.

- Bibliography entries retain all three named authors where supplied. Several later records use `/tree/main/` and three entries use only repository-relative local paths (10700–10723). For a published evidence record, pin these to immutable revisions and provide accessible archive links once those exact revisions are available. This is a reproducibility recommendation, not a finding that any cited record is absent. Do not alter citation keys, authorship or document metadata during this cleanup.

## Mathematical and proof-status observations

The written next-length, joining, fixed/moving-endpoint accounting, controlled-map, slice-compatibility, two-coordinate classification, three-coordinate extension, domain-capacity, tight-partner and joint-support arguments are coherent on inspection under their stated hypotheses. In particular:

- The construction text keeps edge counts separate from vertex counts, retains crossing compatibility, and recognizes disconnected face forests.
- Native closure of the 131 saved classes is consistently scoped to specified move families. The text does not promote closure, repeated recovery or endpoint blocking to classification of all snakes.
- Same-endpoint length parity, the distinction between deletion count and span, and the difference between exact-length exclusions and exclusion of all longer constrained paths are correctly preserved.
- The general geometric results and the finite data supporting source-specific rigidity have different verification scopes. The text explicitly records these limits at 6204–6211, 6371–6378, 6453–6464, 6535–6541 and 6599–6605. These limits should survive condensation.
- The subset and partner deductions retain necessary distinctness, domain containment and partner-completeness premises. The later source-specific compositions are not presented as complete certificates of the native search traversal.
- The round-219 potential argument proves all-cycle occupancy feasibility by telescoping a potential around each cycle after deleting one edge. The convex combination preserves the linear constraints and gives total weight 94. This establishes a limitation of that continuous relaxation, with no claim of a compatible path or global bound. The exact rational tables and arrays were read as supplied claims, not recomputed here.
- The three-count geometric classification at 8945–9127 is explicitly a proof outline. The review read the entire outline, including its twenty residual families, but did not independently reconstruct every omitted finite branch or replay the archived proof. The same limitation applies to archived computer-assisted upper-bound chains.

No new counterexample to a stated main construction theorem was established in this review. That conclusion has the inspection limits above and is not a certification of all archived computations.

## Edit boundary

Only this review log and the separate frontier-review log are written by this reviewer. No manuscript, theorem label, reference key, author line or `hypersetup` metadata is changed. Any later editorial move must preserve all three authors and every existing label.
