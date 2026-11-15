# Lean framework for context share thresholds (toward an unconditional 231)

Milestone 35, 15 November 2026. The number 34 was already taken (`34-replay-migration`).

On 15 November the solver bound reached m ≤ 231 (milestone 28, `farm231.py`). It uses *context share
thresholds* (ctx 7 and ctx 8, `milestones/28-combined-identities/share7.py`), which the Lean chain of
the unconditional 233 (milestone 33) cannot consume. This milestone designs the Lean extension and
proves it end to end on a toy instance.

## Status

**The extension is feasible, and its generic part is done.** The extension covers both ctx 7 and
ctx 8, with no larger automaton state. The generic framework is written and compiles: about 1,090
lines of Lean in 5 new modules, with no `sorry`, no `native_decide` and no new axiom. A toy chain also
compiles. It goes from two real CaDiCaL LRAT refutations, a ctx 7 key and a ctx 8 key, each replayed
by checker v3, through the new bridge, cover and step check, to a bound with no premises:

```
theorem Snake9.upper_254_toy6SC {m : Nat} (p : Snake m) : m ≤ 254
'Snake9.upper_254_toy6SC' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`bash milestones/35-231-lean/scripts/build_toy.sh DIR` rebuilds everything new from source into `DIR`
in about 2 minutes, one `lean` at a time, and runs the axiom audit:

| theorem | axioms |
|---|---|
| `Snake9.LocalWindow.TagsSW.soundSC` (ctx clause soundness) | propext, Classical.choice, Quot.sound |
| `Snake9.LocalWindow.refuted_share_from_dir` (certificate to snake window) | propext, Classical.choice, Quot.sound |
| `Snake9.DirectionWindow6SC.ctxOK7_of_refuted`, `ctxOK8_of_refuted` | propext, Classical.choice, Quot.sound |
| `Snake9.DirectionWindow6SC.ctx_windows6SC` (both bounds for step n) | propext, Classical.choice, Quot.sound |
| `Snake9.WindowAutomaton.total_bound6SC` (telescoping with `S5C`) | propext, Quot.sound |
| `Snake9.WindowAutomaton.check6SCAt_of_W` (witness shard check, codes 13/14) | propext, Quot.sound |
| `Snake9.upper_of_refuted6SC` (generic 231-shape theorem) | propext, Classical.choice, Quot.sound |
| `Snake9.DirectionWindow6SC.ctx7_C70123412A236664K15`, `ctx8_C801234032A544643K15` (the two certificates) | propext, Classical.choice, Quot.sound |
| `Snake9.DirectionWindow6SC.label6SCToy` (one full label of 7,776 transitions through `check6SCAtW`) | propext, Quot.sound |
| `Snake9.upper_254_toy6SC` | propext, Classical.choice, Quot.sound |

The builds read the existing `.olean` files of the core (`work/final_lean/.lake/build/lib/lean`) and of
the 233 chain (`work/spectral/.verification/chain`). They write only to the scratch directory. No
audited 233 module, lake manifest or toolchain file was touched.

What remains for a real 231 is generated content: tables, shards, covers, a few thousand certificates
and their glue. The remaining Lean work is mechanical; see [Work breakdown](#e-work-breakdown).

## What a transition knows

The 233 automaton (`WindowAutomaton6SDefs`) has two parts:

- **State.** The canonical 7-direction shape `d(n..n+6)` and the counts `a(n+2..n+6)`. That is 34
  shapes × 6^5 counts.
- **Step.** One more direction `d(n+7)` and the count `s = a(n+7)`.

`check6SAt T c t0` therefore sees the eight directions `c = d(n..n+7)` and the six counts
`[t0, t1, t2, t3, t4, s] = a(n+2..n+7)`. A ctx record needs exactly that:

- **ctx 7** reads `c.drop 1 = d(n+1..n+7)`, all six counts, and the share of the centres `n+3..n+7`.
- **ctx 8** reads `c = d(n..n+7)` and the same six counts. The count at `n+1` is left free, so the
  transition does not need to know it.

**So neither context needs a longer state.** The shards, the potential and the Bellman–Ford stay as in
233. Only the step weight changes:

    S5C T c t = max (share6 T.s (c.drop 2) t.tail) (max (ctx7A T (c.drop 1) t) (ctx8A T c t))

In the Lean chain, a ctx-7-only chain is not simpler in any way that matters: it drops one table and
witness code 14, about 15% of the new lines. Choosing between ctx-7-only and ctx 7 + ctx 8 is purely a
question of certificate cost.

## a. The certificate predicate and clause soundness

`work/final_lean/LocalWindowShareCtx.lean`:

```lean
def RefutedShareFrom (window : List Nat) (bounds : List (Nat × Nat)) (M cap k : Nat) : Prop :=
  ∀ S E : Nat → Bool, Axioms S E window (centresOf window bounds) →
    shareSum M S ((centresOf window bounds).drop k) ≤ cap → False
theorem refutedShareFrom_zero_iff : RefutedShareFrom w b M cap 0 ↔ RefutedShare w b M cap
```

Every centre keeps its count bounds. The share cap applies to the centres from index `k` on.

| | window | bounds | `k` | share centres |
|---|---|---|---|---|
| ctx 7 key `(dirs, t, K)` | `winOf dirs` (7 directions, 6 centres) | `boundsOf t` | 1 | the last 5 |
| ctx 8 key `(dirs, t, K)` | `winOf dirs` (8 directions, 7 centres) | `(1, 21) :: boundsOf t` | 2 | the last 5 |

For ctx 8 the free count is the explicit pair `(1, 21)`. The bridge discharges it with
`1 ≤ coreAlpha p (n+1)` (an interior vertex) and `coreAlpha_le_21`. It is not encoded as an uncounted
vertex, as H8 does. An uncounted vertex would drop the lower bound 1, which the solver's CNF uses
(`share7.FREE`).

The statements are `RefutedCtx7 k := RefutedShareFrom (winOf k.1) (boundsOf k.2.1) 12 k.2.2 1` and
`RefutedCtx8 k := RefutedShareFrom (winOf k.1) ((1, 21) :: boundsOf k.2.1) 12 k.2.2 2`, both in
`DirectionWindowBridge6SC`.

**Clause soundness: what is reused and what is new.**

- **Reused unchanged.**
  - From `LocalWindowTagsSW`: every clause-family lemma, that is `old_clause`, `sound_emptyE`,
    `sound_totUp`, `sound_totDown`, `sound_shareCl` and `sound_shareCap`, as well as `totOK`,
    `ckAllS`, `ckAllS_append`, `getF`/`getSF` and `tauS`.
  - From `LocalWindowTagsSharePacked`: `tagsOfSL` and `natsOf`.

  The family lemmas are stated for an arbitrary centre list `cens`. The only kind that reads the
  centre list is the cap totalizer (`TotKind.cap spec`, through `capL cens spec`).
- **New**, in about 100 lines: `checkAllSC`, `sound_clauseSC`, `sound_allSC`, `soundSC`,
  `checkAllSC_of_parts` and `refutedShareFrom_of_sat`. The "centre-range parameter" is just this: the
  counters are checked against `centresK w b`, and the totalizers against `(centresK w b).drop k`.

```lean
def TagsSW.checkAllSC (M X Mr cs tots w b k cap tags raw) : Bool :=
  allK (ctrOKK M (centresK w b)) cs && tots.all (totOK M X w ((centresK w b).drop k)) &&
    ckAllS M X Mr cs tots w cap tags raw
theorem TagsSW.soundSC ... (h : checkAllSC ... = true) (S E) (ax : Axioms S E w (centresOf w b))
    (hc : shareSum Mr S ((centresOf w b).drop k) ≤ cap) : cnfTrue (tauS ...) (raw.map (·.map decodeLit)) = true
theorem TagsSW.refutedShareFrom_of_sat (hsat : ∀ S E, Axioms .. → shareSum .. (drop k) ≤ cap → ∃ τ, cnfTrue τ f)
    (hunsat : Unsat f) : RefutedShareFrom window bounds Mr cap k
```

**The CNF.** `ctxcert.py` builds it with `TaggedShareCtx`. This is `share233.TaggedShare` with the
share part (empty squares, the totalizers, the thresholds `u q t` and the cap totalizer) built only
for the centres of index ≥ `k`; its `spec` therefore has 5 entries. It is `share7.SubShareEncoding` up
to the variable numbering. For the ctx 7 sample the full CNF has the same 105,739 clauses and 13,761
variables as the solver record. The replay is unchanged: checker v3 (`gen_lean_lrat_v3.py`), with the
top-level module directories renamed to `LocalWindowCtxCnf` and `LocalWindowCtxUnsat`, so that a
scratch `LEAN_PATH` root is not shadowed by the core's `LocalWindowCnf/`.

## b. The semantic bridge

**Certificate to window**, in `LocalWindowShareCtx`:

```lean
theorem refuted_share_from_dir (h : RefutedShareFrom (winOf cs) bounds M K k) (p : Snake m) (r)
    (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m) (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j < cs.length, cs.getD j 0 < u.length ∧ u.getD (cs.getD j 0) 0 = dir p (r + j))
    (hb : ∀ i < bounds.length, (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧ coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) :
    K + 1 ≤ ((List.range (bounds.length - k)).map fun i => coreShare M p (r + k + i + 1)).sum
```

- **Reused unchanged:** `frame_axioms` and `frame_window` (`LocalWindowBridge`), `shareLocal_frame`
  (`LocalWindowShareBridge`), `canon_winOf` and `mkPerm_spec`.
- **New:**
  - `shareSum_window_from`, the share sum over the dropped centres as a snake sum, with a
    `drop_map_range` lemma;
  - `refuted_share_from_bridge`, the analogue of `refuted_share_bridge`;
  - `refuted_share_from_dir`, the analogue of `refuted_share_dir`, but for an arbitrary bounds list.

**Window semantics**, in `DirectionWindowBridge6SC`:

```lean
def CtxOK7 (c t : List Nat) (L : Nat) : Prop := ∀ m (p : Snake m) r, r + 7 ≤ m →
  canon (dsOf p r 7) = c → symsOf p r 7 = t → L ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+2)).sum
def CtxOK8 (c t : List Nat) (L : Nat) : Prop := ∀ m (p : Snake m) r, r + 8 ≤ m →
  canon (dsOf p r 8) = c → (symsOf p r 8).drop 1 = t → 1 ≤ coreAlpha p (r+1) →
  L ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+3)).sum
theorem ctxOK7_of_refuted (h : RefutedCtx7 (c, t, K)) : CtxOK7 c t (K + 1)
theorem ctxOK8_of_refuted (h : RefutedCtx8 (c, t, K)) : CtxOK8 c t (K + 1)
theorem ctx_windows6SC (hs7 : ∀ k ∈ ks7, RefutedCtx7 k) (hc7 : CtxCover 7 T.cbits (rowf7 T) ks7)
    (hs8 : ∀ k ∈ ks8, RefutedCtx8 k) (hc8 : CtxCover 8 T.cbits (rowf8 T) ks8) (hpos) (n) (hn : n + 8 ≤ m) :
  max (ctx7A T ((win8s6 (pathDir p) n).drop 1) (syms6s6 (coreAlpha p) n))
      (ctx8A T (win8s6 (pathDir p) n) (syms6s6 (coreAlpha p) n)) ≤ coreShare 12 p (n+3) + … + coreShare 12 p (n+7)
```

**Orientation.**

- **ctx keys.** The ctx bounds have no reversed case. `ctx7_window` and `ctx8_window` apply the key to
  the window read in the path direction. `share_window6`, by contrast, also uses `dsOf_rev`,
  `symsOf_rev` and `coreShare_window_rev`; none of these is needed for ctx.
- **5-window part.** It is still `share6`, the maximum over both orientations, through the unchanged
  `share_windows6S`.
- **Relabelling.** Both ctx tables and the keys are indexed by the canonical first-occurrence
  relabelling: `shapeCode (canon ds)` in the table, `canon (dsOf p r n) = c` in the semantics, and
  `k.1 == c` in `keyLevel`, which is reused from `DirectionWindowBridge6S`. This is `refine.canon`,
  the function `share7.ctx_index` uses.

## c. Automaton, step check and cover

**Tables**, in `WindowAutomaton6SCDefs`:

```lean
structure Tables6SC where
  s : Tables6S                 -- the 233 tables, unchanged (k6, H8, 5-window shares, potential, λ)
  c7Idx : Nat → Nat            -- 7-direction shape code ↦ ctx 7 row
  c7 : Nat → Nat → Nat         -- row, t0 ↦ cbits-wide fields at cntIdx6 [t1, t2, t3, t4, s] (6^5 fields)
  c8Idx : Nat → Nat            -- 8-direction shape code ↦ ctx 8 row
  c8 : Nat → Nat → Nat
  cbits : Nat
def ctx7A T ds t := ctxAt T.cbits (T.c7 (T.c7Idx (shapeCode (canon ds)))) t   -- oriented
def ctx8A T ds t := ctxAt T.cbits (T.c8 (T.c8Idx (shapeCode (canon ds)))) t
```

Each key occupies exactly one field, so the tables are dense rows of 7,776 fields. They are not trees,
because a transition needs a value, not a membership test.

**Step check.** `check6SCAt` is `check6SAt` with `S5C` in place of `share6`. The other definitions are
copies with `w6SC`: `StepOK6SC`, `ShardsOK6SC`, `check6SC_of_shards`, `step6SC_raw`, `invariant6SC`
and `total_bound6SC`. The invariant proof obligation is unchanged except for one transport lemma,
`S5C_canon : S5C T (canon x) t = S5C T x t`, which is proved.

**Witness codes**, in `WindowAutomaton6SCV2`. The 4-bit code of `check6SAtW` has three free values,
13 to 15, and two of them are used:

- **13**: the step inequality with `fld5 T.cbits r7 t1 t2 t3 t4 s`, the ctx 7 field;
- **14**: the step inequality with the ctx 8 field;
- **0 to 12**: `tr6SF`, unchanged, lifted to `S5C` by `lift6SC`.

The rows `r7 = T.c7 (T.c7Idx (shapeCode (canon (c.drop 1)))) t0` and
`r8 = T.c8 (T.c8Idx (shapeCode (canon c))) t0` depend only on the label `(c, t0)`, so they are bound by
`let` once per label. A field costs one shift and one mask, as code 0 does. The bridge
`check6SCAt_of_W` is proved, and `label6SCToy` runs it on a full label.

**Cover**, the `ShareCover` analogue:

```lean
def ctxRowOK (bits : Nat) (row : Nat → Nat) (ks : List CtxKey) (c : List Nat) (t0 : Nat) : Bool :=
  allSym^5 fun t1 t2 t3 t4 s => Nat.beq (ctxAt bits row [t0,..,s]) 0 || decide (ctxAt bits row [t0,..,s] ≤ keyLevel c [t0,..,s] ks)
def CtxCover (n bits : Nat) (rowf : List Nat → Nat → Nat) (ks : List CtxKey) : Prop :=
  ∀ c, isRGS c 0 = true → c.length = n → ∀ t0 ∈ [1,6], ∃ ksr, (∀ k ∈ ksr, k ∈ ks) ∧ ctxRowOK bits (rowf c) ksr c t0 = true
theorem ctxCover_rows (shapes) (hz : allRGS n 0 (zeroOutsideC rowf shapes) = true)
    (hr : ∀ c ∈ shapes, ∃ i, allSym (ctxRowOK bits (rowf c) (chunks.getD i []) c) = true) : CtxCover n bits rowf chunks.flatten
```

The key list is the concatenation of one chunk per shape. Each row is checked against its own chunk,
and the short-circuit `||` only scans keys at nonzero fields. On the record set of 15 November
(4,834 ctx 7 keys and 508 ctx 8 keys, taking the best UNSAT record per key), the check needs:

- 34 + 52 shape declarations, plus 2 zero checks (`allRGS 7` and `allRGS 8`);
- about 4·10^5 key comparisons (Σ |keys per row|²);
- 6 × 7,776 field tests per shape.

That is small next to the 233 bridge.

**Table sizes on the same records.**

| | keys | nonzero rows | shapes | max T |
|---|---|---|---|---|
| ctx 7 | 4,834 | 140 | 34 | 200 |
| ctx 8 | 508 | 105 | 52 | 150 |

`cbits = 8` suffices, since T ≤ 255. A row is 7,776 × 8 bits = 7.8 KB, so the 245 rows take about
1.9 MB packed, or about 3.8 MB of hex in the data module (233's potential rows were about 2 MB).
The shards keep the 233 count and size: 204 shards, 34 shapes × 6 values of t0 × 9 labels. The only
addition per label is two `let` rows of 62 kbit.

## d. Generator changes

| generator | change | lines (estimate) | risk |
|---|---|---|---|
| `gen_lean_automaton6s.py` → `gen_lean_automaton6sc.py` (copy) | `Tabs`: ctx 7/ctx 8 rows from the plan's ctx levels (`pack`, decode asserts as for `shr`); `shares(X)` returns also `c7 = C7[canon(X[1:])]` over 6^6 and `c8 = C8[canon(X)]`; Bellman–Ford weight `Q (120 s + max(fw, rv, c7, c8))`; witness `0` / `12` / `13` / `14` / exclusion code; the data module emits `c7Idx`, `c7Rows`, `c8Idx`, `c8Rows`, `cbits`, `tables6SC<T>`; the shards call `check6SCAtW` and `check6SC_of_shards` | +120 to 150 | low: mechanical. The Python re-check mirrors `tr6SCF`, and a wrong table only makes a kernel check fail |
| `gen_lean_chain6s.py` → `gen_lean_chain6sc.py` | `ctxZero7/8` (two `allRGS` decides); one `ctxRow7_<i>` / `ctxRow8_<i>` per shape against its chunk; `ctxCover7/8` via `ctxCover_rows`; the aggregate calls `upper_of_refuted6SC` with the premises `AllP RefutedCtx7 ctx7Keys231` and `AllP RefutedCtx8 ctx8Keys231` | +80 | low |
| certificates: `scripts/ctxcert.py` (prototype, done, 236 lines) → a production driver `cert231.py` | `TaggedShareCtx`, Cnf module = `cert233.emit_share` plus a 5-line rewrite to `checkAllSC`/`soundSC` (asserted), checker v3 replay; to add: cores/plan/cnf/replay/final as in `cert233.py` (kind `ctx`), batching (`prod233.py`), glue `LocalWindowCtxUnsat231_<c>` (chunks of about 50 `refutedShareFrom_of_sat` terms) and `allCtx7_231 : AllP RefutedCtx7 ctx7Keys231` | +300, mostly a copy of the share path of `cert233.py` | medium: the run itself (cost, memory, stack); see the risks below |

## e. Work breakdown

| item | status | Lean lines | nature |
|---|---|---|---|
| `LocalWindowShareCtx` (predicate, clause soundness, bridge) | **done** | 230 | real proof (small) |
| `WindowAutomaton6SCDefs` (tables, `S5C`, step test, telescoping) | **done** | 241 | copy and extend |
| `WindowAutomaton6SCV2` (codes 13/14, `check6SCAt_of_W`) | **done** | 144 | copy and extend |
| `DirectionWindowBridge6SC` (`CtxOK7/8`, cover, window bounds) | **done** | 347 | real proof (moderate) |
| `AggregateDirection6SCConditional` (`upper_of_windows6SC`, `upper_of_refuted6SC`, `…_noShare`) | **done** | 125 | glue |
| toy (data, bridge, aggregate, 2 certificates) | **done** | 206 + generated | |
| generators (automaton, chain) | to do | (Python, about 230) | mechanical |
| real data module, 204 shards, bridge, aggregate `AggregateDirection6SC231` | to do | generated | mechanical; about 0.7 CPU-hours of shards, as for 233 |
| ctx certificates: N₇ + N₈ Cnf and replay modules and their glue | to do | generated | **dominant cost** |
| new 5-window share and plain/H8 certificates beyond the 233 ones (from the plan) | to do | generated | as in 233 |
| `UpperBound231.lean`: apply `upper_231_of_…` to `floors233` (`Floors233Port`) and the four certificate premises; audit with `chain_audit.py` | to do | about 30 | glue |

No new real proof is needed for the 231 chain unless the plan asks for a new kind of fact. One option
is a family lemma for ctx keys, an analogue of L1: one certificate with widened count bounds would
cover several lumped count tuples. `RefutedShareFrom` already accepts any bounds list, so this is
about 40 lines (bounds monotonicity), plus a cover that matches keys by bound inclusion.

**Measured on the two toy certificates** (1 `lean` job, `nice -n 10`):

| key | full CNF | core | replay hints | Cnf module | replay module |
|---|---|---|---|---|---|
| ctx 7 `0123412 / 236664`, cap 15 | 105,739 clauses | 591 clauses | 1,870 | 5 to 6 s | 1 s |
| ctx 8 `01234032 / 544643`, cap 15 (record has T = 32) | 109,078 clauses | 7,973 clauses | 204,129 (4 segments) | 27 to 28 s | 33 to 34 s (0.16 ms per hint) |

**What could make it fail or make it expensive:**

1. **Certificate cost.** This is the main risk, and the cost agent's job. Real levels are mostly 24 to
   60, up to 200, against the cap 15 here. One sample per kind says little about the mean.
2. **Cnf module cost.** The ctx certificates are share-type. In 233 the share Cnf modules averaged
   **68.8 s** each (9.36 h for 490 certificates; up to 404 s and 5.3 GB with clause parts of 500 to
   1,000 literals for caps of 24 and above). `certplan231.py` uses `CNF_H_PER_CERT = 12.63/3108` ≈
   14.6 s, the average over seeds and shares, and so probably underestimates this item for ctx
   certificates by about 4.7 times.
3. **Size of the replay sources and `.olean` files.** In 233 this was 2.66 B of `.olean` per hint, and
   the largest certificates needed `leanbig.sh` (1 GB stack) and about 12 GB of RSS.
4. **Kernel stack in shards.** A witness built as a term (`Nat.pow 16 7776 - 1`) overflowed the stack
   here; a `nat_lit` hex literal, as the 233 shards use, compiles. Keep literals.
5. **Field width.** If a level exceeds 255, `cbits` must be 9. That changes only data.
6. **Glue memory.** `LocalWindowShareUnsat6SB233` took 3.12 GB for 490 certificates and
   `LocalWindowDirUnsat6SB233` 11.36 GB for 7,056 keys. A few thousand ctx certificates need chunked
   glue in the same way: 50 to 400 per chunk module, then one aggregate.
7. **Plan semantics.** If the certificate plan uses a level not matching the Lean semantics (wrong
   orientation, non-canonical labels, other bounds), a kernel check fails. It never gives a wrong
   theorem.

## What the certificate plan must respect

- **One automaton, one potential.** The 233 automaton is used unchanged: 34 shapes × 6^5 states,
  6,158,592 canonical transitions in the solver's count. The weight is
  `120 s + max(L5, L7, L8)`, and each transition is justified by one source (one witness code).
- **Key form.** `k7 = (canon(ds[1:8]), t)` and `k8 = (canon(ds[0:8]), t)`, where `canon` is the
  first-occurrence RGS and `t` the 6 lumped counts of vertices n+2..n+7 (6 stands for 6..21).
  Records are oriented: no reversed lookup for ctx records. The 5-window `L5` keeps both orientations.
- **One table value per key.** Each `(ctx, dirs, t)` gets one value, its certificate at cap = level − 1,
  with M = 12 and the share cap on the trailing 5 centres. A lower level than a proved record needs a
  new solve at that cap, or the higher certificate, which already implies it
  (`RefutedShareFrom.anti`).
- **Bounds exactly as in `share7.encode`.** For ctx 7: `boundsOf t`. For ctx 8: `[(1, 21)] + boundsOf t`.
  A `(0, 21)` certificate would also be sound, but `RefutedCtx8` states `(1, 21)`, so it would need its own predicate. The CNF is `TaggedShareCtx` /
  `SubShareEncoding`: radius 4, all centres counted.
- **Levels at most 255**, or the table needs 9-bit fields.
- **No family lemma for ctx keys yet.** Every key needs its own certificate. An L1 analogue (widened
  counts) is cheap to add in Lean if the plan shows it pays.
- **Free certificates.** The 233 certificates are reusable unchanged: plain, H8 and 5-window share
  keys, and the floors `Floors233`.

## Claims not verified by building

- The line and time estimates for the generators and the production run, and the table sizes; the
  table sizes are computed from the records, but no real data module was generated.
- That the real shards stay at about the 233 cost. The only added work per label is the two `let`
  rows, and only one label, `label6SCToy`, was checked.
- The real 231 chain itself: no real tables, shards or plan exist yet.
- That `UpperBound231` can import the floor port and thousands of certificates within 13.35 GiB. The
  233 audit peaked at 12.61 GB.

## Files

- `work/final_lean/LocalWindowShareCtx.lean`: `RefutedShareFrom`, `TagsSW.checkAllSC`/`soundSC`/`refutedShareFrom_of_sat`, `refuted_share_from_dir`.
- `work/spectral/stronger/WindowAutomaton6SCDefs.lean`, `WindowAutomaton6SCV2.lean`, `DirectionWindowBridge6SC.lean`, `AggregateDirection6SCConditional.lean`: the generic framework.
- `work/spectral/stronger/WindowAutomaton6SCToyData.lean`, `DirectionWindowBridge6SCToy.lean`, `AggregateDirection6SCToy.lean`: the toy chain (`upper_254_toy6SC`).
- `milestones/35-231-lean/lean/LocalWindowCtx{Cnf,Unsat}/C70123412A236664K15.lean`, `…/C801234032A544643K15.lean`: the two generated certificates. `*.core.json` holds their metadata: full CNF SHA-256, cuts and core ids, so they can be regenerated.
- `milestones/35-231-lean/scripts/ctxcert.py`: ctx certificate generator. Usage: `ctxcert.py --out DIR 7 0123412 236664 15 8 01234032 544643 15`, with `CTXCERT_SCR` as the work directory.
- `milestones/35-231-lean/scripts/build_toy.sh`: clean build plus axiom audit.
