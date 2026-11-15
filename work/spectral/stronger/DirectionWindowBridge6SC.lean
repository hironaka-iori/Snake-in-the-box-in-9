/-
The context share window bounds of a share-weighted six-centre automaton with context shares
(`WindowAutomaton6SCDefs`), from its certificates, for an arbitrary table bundle `T : Tables6SC`.
Milestone 35 (`milestones/35-231-lean/DESIGN.md`, item b).

Core Lean only.  Two new certificate types (`LocalWindowShareCtx`):

* **ctx 7 keys** `(dirs, t, K)`, 7 directions and the 6 lumped counts of the 6 centres:
  `RefutedCtx7 k = RefutedShareFrom (winOf dirs) (boundsOf t) 12 K 1`, i.e. on every fitting
  window the M = 12 share sum of the last 5 centres is at least `K + 1` (`ctxOK7_of_refuted`);
* **ctx 8 keys** `(dirs, t, K)`, 8 directions and the 6 lumped counts of the last 6 of the 7
  centres: `RefutedCtx8 k = RefutedShareFrom (winOf dirs) ((1, 21) :: boundsOf t) 12 K 2`; the
  first centre's count is free (`1 ≤ α ≤ 21`, the bounds list starts with `(1, 21)`), the share
  cap is on the last 5 centres (`ctxOK8_of_refuted`).

Both are **oriented**: a key applies only to windows read in the path direction (no reversal),
with the canonical (first-occurrence) relabelling of the directions.

`CtxCover n bits rowf ks` (the analogue of `ShareCover`): every field of the ctx rows of every
canonical `n`-direction shape is 0 or at most `keyLevel c t ksr` for a sublist `ksr` of the keys.
It is checked row by row (`ctxCover_rows`, one cheap kernel evaluation that the rows outside a
listed set of shapes are zero, one declaration per listed shape against one chunk of keys).
`ctx7_window`, `ctx8_window` bound the table values of every snake window by the trailing share
sum, and `ctx_windows6SC` puts both into the shape of the premise `hS5` of
`Combined.combined_bound` for the step `n` (centres `n+3 .. n+7`).
-/
import DirectionWindowBridge6S
import WindowAutomaton6SCDefs
import LocalWindowShareCtx

namespace Snake9.DirectionWindow6SC
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
  Snake9.DirectionWindow6 Snake9.DirectionWindow6S

set_option maxHeartbeats 1000000

/-- A context share key: canonical directions, six lumped counts, cap. -/
abbrev CtxKey := List Nat × List Nat × Nat

/-- The certificate statement of a ctx 7 key (share cap on the centres from index 1 on). -/
def RefutedCtx7 (k : CtxKey) : Prop := RefutedShareFrom (winOf k.1) (boundsOf k.2.1) 12 k.2.2 1

/-- The certificate statement of a ctx 8 key: first count free, share cap from index 2 on. -/
def RefutedCtx8 (k : CtxKey) : Prop :=
  RefutedShareFrom (winOf k.1) ((1, 21) :: boundsOf k.2.1) 12 k.2.2 2

/-! ## Semantics of one key -/

/-- On every snake window of 7 directions with canonical shape `c` and lumped counts `t`, the share
sum of its last 5 centres `r+2 .. r+6` is at least `L`. -/
def CtxOK7 (c t : List Nat) (L : Nat) : Prop :=
  ∀ (m : Nat) (p : Snake m) (r : Nat), r + 7 ≤ m → canon (dsOf p r 7) = c → symsOf p r 7 = t →
    L ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+2)).sum

/-- On every snake window of 8 directions with canonical shape `c` and lumped counts `t` of the
centres `r+2 .. r+7` (the count at `r+1` only positive), the share sum of the last 5 centres
`r+3 .. r+7` is at least `L`. -/
def CtxOK8 (c t : List Nat) (L : Nat) : Prop :=
  ∀ (m : Nat) (p : Snake m) (r : Nat), r + 8 ≤ m → canon (dsOf p r 8) = c →
    (symsOf p r 8).drop 1 = t → 1 ≤ coreAlpha p (r+1) →
    L ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+3)).sum

section Relabel
variable {m : Nat} (p : Snake m)

/-- The first-occurrence relabelling of a snake window, in the form `refuted_share_from_dir` takes. -/
theorem relabel (r n : Nat) (hn : r + n ≤ m) :
    ∀ j, j < (canon (dsOf p r n)).length → (canon (dsOf p r n)).getD j 0 < (seenAfter [] (dsOf p r n)).length ∧
      (seenAfter [] (dsOf p r n)).getD ((canon (dsOf p r n)).getD j 0) 0 = dir p (r + j) := by
  have hlen := length_dsOf p r n
  have hmem : ∀ j, j < n → (dsOf p r n).getD j 0 ∈ seenAfter [] (dsOf p r n) := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  intro j hj
  rw [length_canon] at hj
  have e : (canon (dsOf p r n)).getD j 0 = idx (seenAfter [] (dsOf p r n)) ((dsOf p r n).getD j 0) := by
    rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [e]
  refine ⟨idx_lt_of_mem _ _ (hmem j (by omega)), ?_⟩
  rw [getD_idx _ _ (hmem j (by omega)), getD_dsOf p (by omega)]

theorem seen_lt (r n : Nat) (hn : r + n ≤ m) : ∀ d ∈ seenAfter [] (dsOf p r n), d < 9 := by
  intro d hd
  rcases mem_seenAfter_cases [] _ d hd with h | h
  · simp at h
  · simp only [dsOf, List.mem_map, List.mem_range] at h
    obtain ⟨j, hj, rfl⟩ := h
    exact dir_lt p (by omega)

end Relabel

/-- A ctx 7 certificate with cap `K` gives the level `K + 1`. -/
theorem ctxOK7_of_refuted {c t : List Nat} {K : Nat} (h : RefutedCtx7 (c, t, K)) : CtxOK7 c t (K + 1) := by
  intro m p r hr hc ht
  subst hc ht
  have h : RefutedShareFrom (winOf (canon (dsOf p r 7))) (boundsOf (symsOf p r 7)) 12 K 1 := h
  have hres := refuted_share_from_dir h p r (u := seenAfter [] (dsOf p r 7))
    (by simp [boundsOf, length_symsOf, length_canon, length_dsOf]) (by rw [length_canon, length_dsOf]; omega)
    (seenAfter_nodup [] _ List.nodup_nil) (seen_lt p r 7 (by omega)) (relabel p r 7 (by omega)) (by
      intro i hi
      have h6 : i < 6 := by simp [boundsOf, length_symsOf] at hi; omega
      have hi' : i < (symsOf p r 7).length := by rw [length_symsOf]; omega
      rw [getD_boundsOf hi', getD_symsOf p (n := 7) (by omega)]
      exact boundOf_symC (coreAlpha_le_21 p (by omega) (by omega)))
  have e : (boundsOf (symsOf p r 7)).length - 1 = 5 := by simp [boundsOf, length_symsOf]
  rw [e] at hres
  have e2 : (fun i => coreShare 12 p (r + 1 + i + 1)) = (fun i => coreShare 12 p (r + i + 2)) :=
    funext fun i => by rw [show r + 1 + i + 1 = r + i + 2 by omega]
  rw [e2] at hres
  exact hres

theorem getD_drop_symsOf {m : Nat} (p : Snake m) {r n i : Nat} (hi : i + 1 < n - 1) :
    ((symsOf p r n).drop 1).getD i 0 = symC (coreAlpha p (r + i + 2)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    show 1 + i = i + 1 by omega, getD_symsOf p hi]
  rw [show r + (i + 1) + 1 = r + i + 2 by omega]

/-- A ctx 8 certificate with cap `K` gives the level `K + 1`. -/
theorem ctxOK8_of_refuted {c t : List Nat} {K : Nat} (h : RefutedCtx8 (c, t, K)) : CtxOK8 c t (K + 1) := by
  intro m p r hr hc ht h1
  subst hc ht
  have h : RefutedShareFrom (winOf (canon (dsOf p r 8))) ((1, 21) :: boundsOf ((symsOf p r 8).drop 1)) 12 K 2 := h
  have hres := refuted_share_from_dir h p r (u := seenAfter [] (dsOf p r 8))
    (by simp [boundsOf, length_symsOf, length_canon, length_dsOf]) (by rw [length_canon, length_dsOf]; omega)
    (seenAfter_nodup [] _ List.nodup_nil) (seen_lt p r 8 (by omega)) (relabel p r 8 (by omega)) (by
      intro i hi
      have hl : ((1, 21) :: boundsOf ((symsOf p r 8).drop 1)).length = 7 := by
        simp [boundsOf, length_symsOf]
      rw [hl] at hi
      match i, hi with
      | 0, _ =>
        exact ⟨h1, coreAlpha_le_21 p (by omega) (by omega)⟩
      | j + 1, hj =>
        have hj' : j < ((symsOf p r 8).drop 1).length := by simp [length_symsOf]; omega
        rw [List.getD_cons_succ, getD_boundsOf hj', getD_drop_symsOf p (by omega),
          show r + (j + 1) + 1 = r + j + 2 by omega]
        exact boundOf_symC (coreAlpha_le_21 p (by omega) (by omega)))
  have e : ((1, 21) :: boundsOf ((symsOf p r 8).drop 1)).length - 2 = 5 := by
    simp [boundsOf, length_symsOf]
  rw [e] at hres
  have e2 : (fun i => coreShare 12 p (r + 2 + i + 1)) = (fun i => coreShare 12 p (r + i + 3)) :=
    funext fun i => by rw [show r + 2 + i + 1 = r + i + 3 by omega]
  rw [e2] at hres
  exact hres

theorem ctxOK7_mono {c t : List Nat} {L L' : Nat} (h : CtxOK7 c t L) (hl : L' ≤ L) : CtxOK7 c t L' :=
  fun m p r hr hc ht => Nat.le_trans hl (h m p r hr hc ht)

theorem ctxOK8_mono {c t : List Nat} {L L' : Nat} (h : CtxOK8 c t L) (hl : L' ≤ L) : CtxOK8 c t L' :=
  fun m p r hr hc ht h1 => Nat.le_trans hl (h m p r hr hc ht h1)

/-- The keys of a list (each backed by its certificate) give the level `keyLevel c t ks`. -/
theorem ctxOK7_keyLevel (c t : List Nat) : ∀ (ks : List CtxKey), (∀ k ∈ ks, RefutedCtx7 k) →
    CtxOK7 c t (keyLevel c t ks)
  | [], _ => fun _ _ _ _ _ _ => Nat.zero_le _
  | k :: ks, h => by
    unfold keyLevel
    have ih := ctxOK7_keyLevel c t ks (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    cases hk : (k.1 == c && k.2.1 == t)
    · exact ih
    · simp only [Bool.and_eq_true, beq_iff_eq] at hk
      have h1 := h k List.mem_cons_self
      have h1' : RefutedCtx7 (c, t, k.2.2) := by rw [← hk.1, ← hk.2]; exact h1
      have hk1 := ctxOK7_of_refuted h1'
      intro m p r hr hc ht
      exact Nat.max_le.2 ⟨hk1 m p r hr hc ht, ih m p r hr hc ht⟩

theorem ctxOK8_keyLevel (c t : List Nat) : ∀ (ks : List CtxKey), (∀ k ∈ ks, RefutedCtx8 k) →
    CtxOK8 c t (keyLevel c t ks)
  | [], _ => fun _ _ _ _ _ _ _ => Nat.zero_le _
  | k :: ks, h => by
    unfold keyLevel
    have ih := ctxOK8_keyLevel c t ks (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    cases hk : (k.1 == c && k.2.1 == t)
    · exact ih
    · simp only [Bool.and_eq_true, beq_iff_eq] at hk
      have h1 := h k List.mem_cons_self
      have h1' : RefutedCtx8 (c, t, k.2.2) := by rw [← hk.1, ← hk.2]; exact h1
      have hk1 := ctxOK8_of_refuted h1'
      intro m p r hr hc ht h1
      exact Nat.max_le.2 ⟨hk1 m p r hr hc ht h1, ih m p r hr hc ht h1⟩

/-! ## The context cover -/

/-- Every field of the ctx row family `row` (first count `t0`) of the shape `c` is 0 or backed by
the keys `ks`. -/
def ctxRowOK (bits : Nat) (row : Nat → Nat) (ks : List CtxKey) (c : List Nat) (t0 : Nat) : Bool :=
  allSym (fun t1 => allSym (fun t2 => allSym (fun t3 => allSym (fun t4 => allSym (fun s =>
    Nat.beq (ctxAt bits row [t0, t1, t2, t3, t4, s]) 0 ||
    decide (ctxAt bits row [t0, t1, t2, t3, t4, s] ≤ keyLevel c [t0, t1, t2, t3, t4, s] ks))))))

/-- The cover of a ctx table (`rowf c` the row family of the canonical `n`-direction shape `c`). -/
def CtxCover (n bits : Nat) (rowf : List Nat → Nat → Nat) (ks : List CtxKey) : Prop :=
  ∀ c, isRGS c 0 = true → c.length = n → ∀ t0, 1 ≤ t0 → t0 ≤ 6 →
    ∃ ksr : List CtxKey, (∀ k ∈ ksr, k ∈ ks) ∧ ctxRowOK bits (rowf c) ksr c t0 = true

/-- The row families of the two ctx tables. -/
def rowf7 (T : Tables6SC) (c : List Nat) : Nat → Nat := T.c7 (T.c7Idx (shapeCode c))
def rowf8 (T : Tables6SC) (c : List Nat) : Nat → Nat := T.c8 (T.c8Idx (shapeCode c))

/-- The rows of the shapes outside `shapes` are zero. -/
def zeroOutsideC (rowf : List Nat → Nat → Nat) (shapes : List (List Nat)) (c : List Nat) : Bool :=
  allSym (fun t0 => rowf c t0 == 0) || decide (c ∈ shapes)

theorem ctxRowOK_of_zero (bits : Nat) (row : Nat → Nat) (ks : List CtxKey) (c : List Nat) (t0 : Nat)
    (h : row t0 = 0) : ctxRowOK bits row ks c t0 = true := by
  unfold ctxRowOK
  refine allSym_of_forall _ (fun t1 _ _ => allSym_of_forall _ (fun t2 _ _ =>
    allSym_of_forall _ (fun t3 _ _ => allSym_of_forall _ (fun t4 _ _ =>
    allSym_of_forall _ (fun s _ _ => ?_)))))
  simp [ctxAt, h]

theorem mem_flatten_getD' {α : Type} {chunks : List (List α)} {i : Nat} {k : α}
    (h : k ∈ chunks.getD i []) : k ∈ chunks.flatten := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hc : chunks[i]? with
  | none => rw [hc] at h; exact absurd h List.not_mem_nil
  | some L =>
    rw [hc] at h
    exact List.mem_flatten.2 ⟨L, List.mem_of_getElem? hc, h⟩

/-- `CtxCover` from one kernel evaluation (rows outside `shapes` are zero) and one declaration per
listed shape, each against one chunk of the keys. -/
theorem ctxCover_rows {n bits : Nat} {rowf : List Nat → Nat → Nat} {chunks : List (List CtxKey)}
    (shapes : List (List Nat)) (hz : allRGS n 0 (zeroOutsideC rowf shapes) = true)
    (hr : ∀ c ∈ shapes, ∃ i, allSym (ctxRowOK bits (rowf c) (chunks.getD i []) c) = true) :
    CtxCover n bits rowf chunks.flatten := by
  intro c hc hl t0 h1 h6
  have h := allRGS_spec n 0 _ hz c hl hc
  unfold zeroOutsideC at h
  rcases Bool.or_eq_true_iff.1 h with h0 | hm
  · exact ⟨[], fun _ hk => absurd hk List.not_mem_nil,
      ctxRowOK_of_zero bits _ [] c t0 (by simpa using allSym_spec _ h0 t0 h1 h6)⟩
  · obtain ⟨i, hi⟩ := hr c (of_decide_eq_true hm)
    exact ⟨chunks.getD i [], fun _ hk => mem_flatten_getD' hk, allSym_spec _ hi t0 h1 h6⟩

/-- A cover bounds each field by the level of some backed sublist of the keys. -/
theorem ctxCover_spec {n bits : Nat} {rowf : List Nat → Nat → Nat} {ks : List CtxKey}
    (hc : CtxCover n bits rowf ks) {c t : List Nat} (hr : isRGS c 0 = true) (hl : c.length = n)
    (ht : t.length = 6) (hb : ∀ x ∈ t, 1 ≤ x ∧ x ≤ 6) :
    ∃ ksr : List CtxKey, (∀ k ∈ ksr, k ∈ ks) ∧ ctxAt bits (rowf c) t ≤ keyLevel c t ksr := by
  match t, ht, hb with
  | [t0, t1, t2, t3, t4, s], _, hb =>
    have b0 := hb t0 (by simp)
    have b1 := hb t1 (by simp)
    have b2 := hb t2 (by simp)
    have b3 := hb t3 (by simp)
    have b4 := hb t4 (by simp)
    have b5 := hb s (by simp)
    obtain ⟨ksr, hsub, hrow⟩ := hc c hr hl t0 b0.1 b0.2
    refine ⟨ksr, hsub, ?_⟩
    unfold ctxRowOK at hrow
    have h := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ hrow
      t1 b1.1 b1.2) t2 b2.1 b2.2) t3 b3.1 b3.2) t4 b4.1 b4.2) s b5.1 b5.2
    rcases Bool.or_eq_true_iff.1 h with h | h
    · rw [Nat.beq_eq] at h
      rw [h]
      exact Nat.zero_le _
    · exact of_decide_eq_true h

/-! ## Window bounds -/

section Window
variable {m : Nat} (p : Snake m)

theorem symsOf_bounds6 (r n : Nat) (hpos : ∀ i, i < n - 1 → 1 ≤ coreAlpha p (r + i + 1)) :
    ∀ x ∈ symsOf p r n, 1 ≤ x ∧ x ≤ 6 := by
  intro x hx
  simp only [symsOf, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨symC_ge_one (hpos i (by omega)), symC_le_six _⟩

/-- **The ctx 7 window bound**: the ctx 7 level of a snake window of 7 directions (path
orientation) is at most the share sum of its last five centres. -/
theorem ctx7_window {T : Tables6SC} {ks : List CtxKey} (hs : ∀ k ∈ ks, RefutedCtx7 k)
    (hc : CtxCover 7 T.cbits (rowf7 T) ks) (r : Nat) (hr : r + 7 ≤ m)
    (hpos : ∀ i, i < 6 → 1 ≤ coreAlpha p (r + i + 1)) :
    ctx7A T (dsOf p r 7) (symsOf p r 7) ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+2)).sum := by
  obtain ⟨ksr, hsub, hle⟩ := ctxCover_spec (c := canon (dsOf p r 7)) (t := symsOf p r 7) hc (canon_isRGS _)
    (by rw [length_canon, length_dsOf]) (by rw [length_symsOf]) (symsOf_bounds6 p r 7 hpos)
  have hk := ctxOK7_keyLevel (canon (dsOf p r 7)) (symsOf p r 7) ksr (fun k hk => hs k (hsub k hk))
  exact Nat.le_trans hle (hk m p r hr rfl rfl)

/-- **The ctx 8 window bound**: the ctx 8 level of a snake window of 8 directions (path
orientation), counted on its centres `r+2 .. r+7`, is at most the share sum of its last five
centres. -/
theorem ctx8_window {T : Tables6SC} {ks : List CtxKey} (hs : ∀ k ∈ ks, RefutedCtx8 k)
    (hc : CtxCover 8 T.cbits (rowf8 T) ks) (r : Nat) (hr : r + 8 ≤ m)
    (hpos : ∀ i, i < 7 → 1 ≤ coreAlpha p (r + i + 1)) :
    ctx8A T (dsOf p r 8) ((symsOf p r 8).drop 1) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+i+3)).sum := by
  have hb : ∀ x ∈ (symsOf p r 8).drop 1, 1 ≤ x ∧ x ≤ 6 :=
    fun x hx => symsOf_bounds6 p r 8 hpos x (List.mem_of_mem_drop hx)
  obtain ⟨ksr, hsub, hle⟩ := ctxCover_spec (c := canon (dsOf p r 8)) (t := (symsOf p r 8).drop 1) hc
    (canon_isRGS _) (by rw [length_canon, length_dsOf]) (by simp [length_symsOf]) hb
  have hk := ctxOK8_keyLevel (canon (dsOf p r 8)) ((symsOf p r 8).drop 1) ksr (fun k hk => hs k (hsub k hk))
  exact Nat.le_trans hle (hk m p r hr rfl rfl (hpos 0 (by omega)))

/-- Both context bounds of step `n` (centres `n+3 .. n+7`) in the shape of the premise `hS5` of
`Combined.combined_bound`. -/
theorem ctx_windows6SC {T : Tables6SC} {ks7 ks8 : List CtxKey}
    (hs7 : ∀ k ∈ ks7, RefutedCtx7 k) (hc7 : CtxCover 7 T.cbits (rowf7 T) ks7)
    (hs8 : ∀ k ∈ ks8, RefutedCtx8 k) (hc8 : CtxCover 8 T.cbits (rowf8 T) ks8)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ coreAlpha p j) (n : Nat) (hn : n + 8 ≤ m) :
    max (ctx7A T ((win8s6 (pathDir p) n).drop 1) (syms6s6 (coreAlpha p) n))
        (ctx8A T (win8s6 (pathDir p) n) (syms6s6 (coreAlpha p) n)) ≤
      coreShare 12 p (n+3) + coreShare 12 p (n+4) + coreShare 12 p (n+5) + coreShare 12 p (n+6) +
        coreShare 12 p (n+7) := by
  have h7 := ctx7_window p hs7 hc7 (n + 1) (by omega)
    (fun i hi => hpos (n + 1 + i + 1) (by omega) (by omega))
  have h8 := ctx8_window p hs8 hc8 n hn (fun i hi => hpos (n + i + 1) (by omega) (by omega))
  have e7 : ((List.range 5).map fun i => coreShare 12 p (n + 1 + i + 2)).sum =
      coreShare 12 p (n+3) + (coreShare 12 p (n+4) + (coreShare 12 p (n+5) +
        (coreShare 12 p (n+6) + (coreShare 12 p (n+7) + 0)))) := rfl
  have e8 : ((List.range 5).map fun i => coreShare 12 p (n + i + 3)).sum =
      coreShare 12 p (n+3) + (coreShare 12 p (n+4) + (coreShare 12 p (n+5) +
        (coreShare 12 p (n+6) + (coreShare 12 p (n+7) + 0)))) := rfl
  rw [e7] at h7
  rw [e8] at h8
  have d8 : win8s6 (pathDir p) n = dsOf p n 8 := by
    unfold win8s6
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    rfl
  have d7 : (win8s6 (pathDir p) n).drop 1 = dsOf p (n + 1) 7 := by
    rw [d8]; rfl
  have s7 : syms6s6 (coreAlpha p) n = symsOf p (n + 1) 7 := rfl
  have s8 : syms6s6 (coreAlpha p) n = (symsOf p n 8).drop 1 := rfl
  rw [← s8, s7] at h8
  rw [d7, d8, s7]
  omega

end Window

end Snake9.DirectionWindow6SC

#print axioms Snake9.DirectionWindow6SC.ctxOK7_of_refuted
#print axioms Snake9.DirectionWindow6SC.ctxOK8_of_refuted
#print axioms Snake9.DirectionWindow6SC.ctxCover_rows
#print axioms Snake9.DirectionWindow6SC.ctx7_window
#print axioms Snake9.DirectionWindow6SC.ctx8_window
#print axioms Snake9.DirectionWindow6SC.ctx_windows6SC
