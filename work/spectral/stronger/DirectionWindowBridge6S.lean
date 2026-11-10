/-
The window premises and the share window bounds of a share-weighted six-centre automaton
(`WindowAutomaton6SDefs`) from its certificates, for an arbitrary table bundle `T : Tables6S`.

Core Lean only.  Three certificate types and one set of floor theorems:

* **plain k6 keys** (`keys`): windows of 3..7 directions, fully counted, as in
  `DirectionWindowBridge6` (`Cover6 T.k6 keys`, here also chunk by chunk: `cover6_chunks`);
* **H8 keys** (`hkeys`): the 8-direction step window with 6 counts, stored reversed (uncounted
  vertex last); `CoverH8 T hkeys` (the search tree holds exactly their codes), `no_forb_H8` via
  `DirectionWindow7.refuted_dirH`;
* **share thresholds** (`skeys`, `AllRefutedShareList`): `(dirs, syms, K)` with the certificate
  `RefutedShare (winOf dirs) (boundsOf syms) 12 K`, i.e. on every fitting window the M = 12 share
  sum of the 5 centres is at least `K + 1` (`shareOK_of_refuted`, via `refuted_share_dir`);
* **share floors of origin/main** (`Floors233`): the universal share-16 floor on 012032
  (milestone 152, `Snake9.ShareTransfer152.share16`), on 012031, 012304 and 012314 (milestone 73,
  `Snake9.CatalogueIntegration73.canonical7300/7304/7306`), and the count-conditioned share-17
  floor on 012032 (milestone 155, `Snake9.CriticalShare155.share17`).  Their statements are
  copied verbatim (`ShareFloor16`, `ShareFloor17`); their proofs (hundreds of replay modules on
  main) are NOT ported, so they are explicit premises of the conditional theorem.

`cover6S` in the plan is `ShareCover T skeys`: every field `L` of a share row of a canonical
6-direction shape `c` and counts `t` (all in 1..6) satisfies `L ≤ floorLevel c t` or
`L ≤ keyLevel c t skeys` (the largest `K + 1` of a share key `(c, t, K)`).  It is checked shape by
shape (`shareCover_rows`).  `share_window6` then bounds the share level `share6` of every snake
window (either orientation) by the window's share sum, which is the premise `hS5` of
`Combined.combined_bound`.
-/
import WindowAutomaton6SDefs
import DirectionWindowBridge7
import LocalWindowShareBridge

namespace Snake9.LocalWindow

/-- Every share key `(dirs, syms, K)` of the list is refuted with cap `K` at resolution 12. -/
def AllRefutedShareList : List (List Nat × List Nat × Nat) → Prop
  | [] => True
  | k :: ks => RefutedShare (winOf k.1) (boundsOf k.2.1) 12 k.2.2 ∧ AllRefutedShareList ks

theorem AllRefutedShareList.mem : ∀ {l : List (List Nat × List Nat × Nat)}, AllRefutedShareList l →
    ∀ k ∈ l, RefutedShare (winOf k.1) (boundsOf k.2.1) 12 k.2.2
  | [], _, k, hk => absurd hk List.not_mem_nil
  | _ :: _, h, k, hk => by
    rcases List.mem_cons.1 hk with rfl | hk
    · exact h.1
    · exact AllRefutedShareList.mem h.2 k hk

end Snake9.LocalWindow

namespace Snake9.DirectionWindow6S
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
  Snake9.DirectionWindow6 Snake9.DirectionWindow7

set_option maxHeartbeats 1000000

/-! ## The floor theorems of origin/main (statements only) -/

/-- The statement of `Snake9.ShareTransfer152.share16` (origin/main, milestone 152, shape
012032) and of `Snake9.CatalogueIntegration73.canonical7300/7304/7306` (milestone 73, shapes
012031, 012304, 012314), for the canonical shape `shape`. -/
def ShareFloor16 (shape : List Nat) : Prop :=
  ∀ {m : Nat} (p : Snake m) (r : Nat), r + 6 ≤ m →
    (canon (dsOf p r 6) = shape ∨ canon (dsOf p r 6).reverse = shape) →
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum

/-- The statement of `Snake9.CriticalShare155.share17` (origin/main, milestone 155). -/
def ShareFloor17 : Prop :=
  ∀ {m : Nat} (p : Snake m) (r : Nat), r + 6 ≤ m →
    ((canon (dsOf p r 6) = [0,1,2,0,3,2] ∧
        coreAlpha p (r+1) = 4 ∧ coreAlpha p (r+2) ≤ 4 ∧
        coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 5 ∧
        coreAlpha p (r+5) = 3) ∨
      (canon (dsOf p r 6).reverse = [0,1,2,0,3,2] ∧
        coreAlpha p (r+1) = 3 ∧ coreAlpha p (r+2) ≤ 5 ∧
        coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 4 ∧
        coreAlpha p (r+5) = 4)) →
    17 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum

/-- The five floor theorems the 233 chain uses (premises; proved on origin/main). -/
structure Floors233 : Prop where
  f012032 : ShareFloor16 [0,1,2,0,3,2]
  f012031 : ShareFloor16 [0,1,2,0,3,1]
  f012304 : ShareFloor16 [0,1,2,3,0,4]
  f012314 : ShareFloor16 [0,1,2,3,1,4]
  f155 : ShareFloor17

/-! ## Window share bounds -/

/-- The share sum of the 5-window `r .. r+6` is at least `L` on every snake window with
canonical directions `c` and lumped counts `t` (forward orientation). -/
def ShareOK (c t : List Nat) (L : Nat) : Prop :=
  ∀ (m : Nat) (p : Snake m) (r : Nat), r + 6 ≤ m → canon (dsOf p r 6) = c → symsOf p r 6 = t →
    L ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum

theorem shareOK_zero (c t : List Nat) : ShareOK c t 0 := fun _ _ _ _ _ _ => Nat.zero_le _

theorem shareOK_mono {c t : List Nat} {L L' : Nat} (h : ShareOK c t L) (hl : L' ≤ L) :
    ShareOK c t L' := fun m p r hr hc ht => Nat.le_trans hl (h m p r hr hc ht)

theorem shareOK_max {c t : List Nat} {a b : Nat} (ha : ShareOK c t a) (hb : ShareOK c t b) :
    ShareOK c t (max a b) := fun m p r hr hc ht => Nat.max_le.2 ⟨ha m p r hr hc ht, hb m p r hr hc ht⟩

/-- A share certificate with cap `K` gives the level `K + 1`. -/
theorem shareOK_of_refuted {c t : List Nat} {K : Nat} (h : RefutedShare (winOf c) (boundsOf t) 12 K) :
    ShareOK c t (K + 1) := by
  intro m p r hr hc ht
  subst hc ht
  have hlen := length_dsOf p r 6
  have hmem : ∀ j, j < 6 → (dsOf p r 6).getD j 0 ∈ seenAfter [] (dsOf p r 6) := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have hres := refuted_share_dir h p r (u := seenAfter [] (dsOf p r 6))
    (by rw [length_canon, length_symsOf, length_dsOf]) (by rw [length_canon]; omega)
    (seenAfter_nodup [] _ List.nodup_nil) (by
      intro d hd
      rcases mem_seenAfter_cases [] _ d hd with h | h
      · simp at h
      · simp only [dsOf, List.mem_map, List.mem_range] at h
        obtain ⟨j, hj, rfl⟩ := h
        exact dir_lt p (by omega)) (by
      intro j hj
      rw [length_canon] at hj
      have e : (canon (dsOf p r 6)).getD j 0 = idx (seenAfter [] (dsOf p r 6)) ((dsOf p r 6).getD j 0) := by
        rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        rfl
      rw [e]
      refine ⟨idx_lt_of_mem _ _ (hmem j (by omega)), ?_⟩
      rw [getD_idx _ _ (hmem j (by omega)), getD_dsOf p (by omega)]) (by
      intro i hi
      exact getD_symsOf p (by rw [length_symsOf] at hi; omega))
  rw [length_symsOf] at hres
  exact hres

theorem symsOf_six {m : Nat} (p : Snake m) (r : Nat) :
    symsOf p r 6 = [symC (coreAlpha p (r+1)), symC (coreAlpha p (r+2)), symC (coreAlpha p (r+3)),
      symC (coreAlpha p (r+4)), symC (coreAlpha p (r+5))] := rfl

theorem eq_of_symC {a : Nat} (h : symC a ≤ 5) : a = symC a := by
  unfold symC at h ⊢
  by_cases ha : a ≤ 6 <;> simp [ha] at h ⊢ <;> omega

theorem symC_ge_one {a : Nat} (h : 1 ≤ a) : 1 ≤ symC a := by
  unfold symC
  split <;> omega

/-- Counts of the milestone-155 floor, in the order of its forward case: `(4, ≤4, 4, ≤5, 3)`. -/
def pat155 : List Nat → Bool
  | [a, b, c, d, e] => a == 4 && Nat.ble b 4 && c == 4 && Nat.ble d 5 && e == 3
  | _ => false

/-- The level that the floor theorems give to the canonical 5-window `c` with counts `t`. -/
def floorLevel (c t : List Nat) : Nat :=
  cond (c == [0,1,2,0,3,2] && (pat155 t || pat155 t.reverse)) 17
    (cond (c == [0,1,2,0,3,2] || c == [0,1,2,0,3,1] || c == [0,1,2,3,0,4] || c == [0,1,2,3,1,4]) 16 0)

theorem shareOK_floor (hF : Floors233) (c t : List Nat) : ShareOK c t (floorLevel c t) := by
  intro m p r hr hc ht
  unfold floorLevel
  cases h17 : (c == [0,1,2,0,3,2] && (pat155 t || pat155 t.reverse))
  · simp only [cond_false]
    cases h16 : (c == [0,1,2,0,3,2] || c == [0,1,2,0,3,1] || c == [0,1,2,3,0,4] || c == [0,1,2,3,1,4])
    · exact Nat.zero_le _
    · simp only [cond_true]
      simp only [Bool.or_eq_true, beq_iff_eq] at h16
      rcases h16 with ((h | h) | h) | h <;> subst h
      · exact hF.f012032 p r hr (Or.inl hc)
      · exact hF.f012031 p r hr (Or.inl hc)
      · exact hF.f012304 p r hr (Or.inl hc)
      · exact hF.f012314 p r hr (Or.inl hc)
  · simp only [cond_true]
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h17
    obtain ⟨rfl, hp⟩ := h17
    rw [← ht, symsOf_six] at hp
    rcases hp with hp | hp
    · simp only [pat155, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hp
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
      refine hF.f155 p r hr (Or.inl ⟨hc, ?_, ?_, ?_, ?_, ?_⟩)
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+1)) ≤ 5)]; exact h1
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+2)) ≤ 5)]; exact h2
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+3)) ≤ 5)]; exact h3
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+4)) ≤ 5)]; exact h4
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+5)) ≤ 5)]; exact h5
    · simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        pat155, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hp
      obtain ⟨⟨⟨⟨h5, h4⟩, h3⟩, h2⟩, h1⟩ := hp
      have hrev : canon (dsOf p r 6).reverse = [0,1,2,0,3,2] := by
        rw [← canon_canon_reverse, hc]
        rfl
      refine hF.f155 p r hr (Or.inr ⟨hrev, ?_, ?_, ?_, ?_, ?_⟩)
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+1)) ≤ 5)]; exact h1
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+2)) ≤ 5)]; exact h2
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+3)) ≤ 5)]; exact h3
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+4)) ≤ 5)]; exact h4
      · rw [eq_of_symC (by omega : symC (coreAlpha p (r+5)) ≤ 5)]; exact h5

/-- The largest `K + 1` over the share keys `(c, t, K)` (0 if there is none). -/
def keyLevel (c t : List Nat) : List (List Nat × List Nat × Nat) → Nat
  | [] => 0
  | k :: ks => cond (k.1 == c && k.2.1 == t) (max (k.2.2 + 1) (keyLevel c t ks)) (keyLevel c t ks)

theorem shareOK_keyLevel (c t : List Nat) : ∀ (ks : List (List Nat × List Nat × Nat)),
    AllRefutedShareList ks → ShareOK c t (keyLevel c t ks)
  | [], _ => shareOK_zero c t
  | k :: ks, h => by
    unfold keyLevel
    cases hk : (k.1 == c && k.2.1 == t)
    · exact shareOK_keyLevel c t ks h.2
    · simp only [Bool.and_eq_true, beq_iff_eq] at hk
      have h1 := h.1
      rw [hk.1, hk.2] at h1
      exact shareOK_max (shareOK_of_refuted h1) (shareOK_keyLevel c t ks h.2)

/-! ## The share cover -/

/-- Every field of the share row `(c, t0)` is backed by a floor or a share key. -/
def shareRowOK (T : Tables6S) (ks : List (List Nat × List Nat × Nat)) (c : List Nat) (t0 : Nat) : Bool :=
  allSym (fun t1 => allSym (fun t2 => allSym (fun t3 => allSym (fun t4 =>
    decide (shareAt6 T (shapeCode c) [t0, t1, t2, t3, t4] ≤ floorLevel c [t0, t1, t2, t3, t4]) ||
    decide (shareAt6 T (shapeCode c) [t0, t1, t2, t3, t4] ≤ keyLevel c [t0, t1, t2, t3, t4] ks)))))

/-- `cover6S` of the plan: every share row of a canonical shape of 6 directions is backed. -/
def ShareCover (T : Tables6S) (ks : List (List Nat × List Nat × Nat)) : Prop :=
  ∀ c, isRGS c 0 = true → c.length = 6 → ∀ t0, 1 ≤ t0 → t0 ≤ 6 → shareRowOK T ks c t0 = true

/-- The share rows of the shapes outside `shapes` are zero. -/
def zeroOutsideS (T : Tables6S) (shapes : List (List Nat)) (c : List Nat) : Bool :=
  allSym (fun t0 => T.shr (T.sIdx (shapeCode c)) t0 == 0) || decide (c ∈ shapes)

theorem shareRowOK_of_zero (T : Tables6S) (ks : List (List Nat × List Nat × Nat)) (c : List Nat)
    (t0 : Nat) (h : T.shr (T.sIdx (shapeCode c)) t0 = 0) : shareRowOK T ks c t0 = true := by
  unfold shareRowOK
  refine allSym_of_forall _ (fun t1 _ _ => allSym_of_forall _ (fun t2 _ _ =>
    allSym_of_forall _ (fun t3 _ _ => allSym_of_forall _ (fun t4 _ _ => ?_))))
  simp [shareAt6, h]

/-- `allSym` from its six values (one declaration per first count in generated modules). -/
theorem allSym_of6 (f : Nat → Bool) (h1 : f 1 = true) (h2 : f 2 = true) (h3 : f 3 = true)
    (h4 : f 4 = true) (h5 : f 5 = true) (h6 : f 6 = true) : allSym f = true := by
  refine allSym_of_forall _ (fun s hs hs' => ?_)
  have : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-- `ShareCover` from one cheap kernel evaluation (the rows outside `shapes` are zero) and one
declaration per listed shape. -/
theorem shareCover_rows {T : Tables6S} {ks : List (List Nat × List Nat × Nat)}
    (shapes : List (List Nat)) (hz : allRGS 6 0 (zeroOutsideS T shapes) = true)
    (hr : ∀ c ∈ shapes, allSym (shareRowOK T ks c) = true) : ShareCover T ks := by
  intro c hc hl t0 h1 h6
  have h := allRGS_spec 6 0 _ hz c hl hc
  unfold zeroOutsideS at h
  rcases Bool.or_eq_true_iff.1 h with h0 | hm
  · exact shareRowOK_of_zero T ks c t0 (by simpa using allSym_spec _ h0 t0 h1 h6)
  · exact allSym_spec _ (hr c (of_decide_eq_true hm)) t0 h1 h6

theorem shareCover_spec {T : Tables6S} {ks : List (List Nat × List Nat × Nat)} (hc : ShareCover T ks)
    (hF : Floors233) (hs : AllRefutedShareList ks) {c t : List Nat} (hr : isRGS c 0 = true)
    (hl : c.length = 6) (ht : t.length = 5) (hb : ∀ x ∈ t, 1 ≤ x ∧ x ≤ 6) :
    ShareOK c t (shareAt6 T (shapeCode c) t) := by
  match t, ht, hb with
  | [t0, t1, t2, t3, t4], _, hb =>
    have b0 := hb t0 (by simp)
    have b1 := hb t1 (by simp)
    have b2 := hb t2 (by simp)
    have b3 := hb t3 (by simp)
    have b4 := hb t4 (by simp)
    have hrow := hc c hr hl t0 b0.1 b0.2
    unfold shareRowOK at hrow
    have h := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ hrow t1 b1.1 b1.2)
      t2 b2.1 b2.2) t3 b3.1 b3.2) t4 b4.1 b4.2
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact shareOK_mono (shareOK_floor hF c _) (of_decide_eq_true h)
    · exact shareOK_mono (shareOK_keyLevel c _ ks hs) (of_decide_eq_true h)

section Window
variable {m : Nat} (p : Snake m)

theorem symsOf_bounds (r : Nat) (hpos : ∀ i, i < 5 → 1 ≤ coreAlpha p (r + i + 1)) :
    ∀ x ∈ symsOf p r 6, 1 ≤ x ∧ x ≤ 6 := by
  intro x hx
  simp only [symsOf, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨symC_ge_one (hpos i (by omega)), symC_le_six _⟩

/-- **The share window bound**: the share level of a snake window (either orientation) is at
most the share sum of its five centres. -/
theorem share_window6 {T : Tables6S} {ks : List (List Nat × List Nat × Nat)} (hF : Floors233)
    (hs : AllRefutedShareList ks) (hc : ShareCover T ks) (r : Nat) (hr : r + 6 ≤ m)
    (hpos : ∀ i, i < 5 → 1 ≤ coreAlpha p (r + i + 1)) :
    share6 T (dsOf p r 6) (symsOf p r 6) ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have hb := symsOf_bounds p r hpos
  unfold share6
  refine Nat.max_le.2 ⟨?_, ?_⟩
  · exact shareCover_spec hc hF hs (canon_isRGS _) (by rw [length_canon, length_dsOf])
      (by rw [length_symsOf]) hb _ p r hr rfl rfl
  · rw [← dsOf_rev p r 6 hr, ← symsOf_rev p r 6 hr]
    have h := shareCover_spec hc hF hs (canon_isRGS _)
      (by rw [length_canon, length_dsOf]) (by rw [length_symsOf]) (by
        rw [symsOf_rev p r 6 hr]
        intro x hx
        exact hb x (List.mem_reverse.1 hx)) _ (revSnake p) (m - r - 6) (by omega) rfl rfl
    have e := coreShare_window_rev 12 p r 5 (by omega)
    rw [show m - r - 5 - 1 = m - r - 6 by omega] at e
    rw [← e]
    exact h

/-- The share bound in the shape of the premise `hS5` of `Combined.combined_bound`. -/
theorem share_windows6S {T : Tables6S} {ks : List (List Nat × List Nat × Nat)} (hF : Floors233)
    (hs : AllRefutedShareList ks) (hc : ShareCover T ks)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ coreAlpha p j) (n : Nat) (hn : n + 8 ≤ m) :
    share6 T [pathDir p (n+2), pathDir p (n+3), pathDir p (n+4), pathDir p (n+5), pathDir p (n+6),
        pathDir p (n+7)]
      [sym (coreAlpha p (n+3)), sym (coreAlpha p (n+4)), sym (coreAlpha p (n+5)),
        sym (coreAlpha p (n+6)), sym (coreAlpha p (n+7))] ≤
      coreShare 12 p (n+3) + coreShare 12 p (n+4) + coreShare 12 p (n+5) + coreShare 12 p (n+6) +
        coreShare 12 p (n+7) := by
  have h := share_window6 p hF hs hc (n + 2) (by omega)
    (fun i hi => hpos (n + 2 + i + 1) (by omega) (by omega))
  have e : ((List.range 5).map fun i => coreShare 12 p (n + 2 + i + 1)).sum =
      coreShare 12 p (n+3) + (coreShare 12 p (n+4) + (coreShare 12 p (n+5) +
        (coreShare 12 p (n+6) + (coreShare 12 p (n+7) + 0)))) := rfl
  rw [e] at h
  rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
  have h' : share6 T [dir p (n+2), dir p (n+3), dir p (n+4), dir p (n+5), dir p (n+6), dir p (n+7)]
      [sym (coreAlpha p (n+3)), sym (coreAlpha p (n+4)), sym (coreAlpha p (n+5)),
        sym (coreAlpha p (n+6)), sym (coreAlpha p (n+7))] ≤ _ := h
  omega

end Window

/-! ## Lists of facts (generated instances prove `AllP P l` by one nested anonymous constructor,
which elaborates much faster than a case split over a long membership) -/

/-- `P` holds for every element of the list, as a nested conjunction. -/
def AllP {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: l => P a ∧ AllP P l

theorem AllP.mem {α : Type} {P : α → Prop} : ∀ {l : List α}, AllP P l → ∀ x ∈ l, P x
  | [], _, x, hx => absurd hx List.not_mem_nil
  | _ :: _, h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact AllP.mem h.2 x hx

/-! ## The k6 cover chunk by chunk -/

/-- `Cover6` for large key sets given in chunks: one kernel evaluation per window length shows
that only the listed rows are nonzero, and each listed row is checked against one chunk. -/
theorem cover6_chunks {T : Tables6} (chunks : List (List (List Nat × List Nat)))
    (rows : List (List Nat × Nat))
    (h3 : allRGS 3 0 (zeroOutside6 T rows) = true) (h4 : allRGS 4 0 (zeroOutside6 T rows) = true)
    (h5 : allRGS 5 0 (zeroOutside6 T rows) = true) (h6 : allRGS 6 0 (zeroOutside6 T rows) = true)
    (h7 : allRGS 7 0 (zeroOutside6 T rows) = true)
    (hr : ∀ r ∈ rows, ∃ i, rowOK6 T (chunks.getD i []) r.1 r.2 = true) :
    Cover6 T chunks.flatten := by
  intro c hc hn1 hn2 s0 hs0
  have hz : zeroOutside6 T rows c = true := by
    have : c.length = 3 ∨ c.length = 4 ∨ c.length = 5 ∨ c.length = 6 ∨ c.length = 7 := by omega
    rcases this with e | e | e | e | e
    · exact allRGS_spec 3 0 _ h3 c e hc
    · exact allRGS_spec 4 0 _ h4 c e hc
    · exact allRGS_spec 5 0 _ h5 c e hc
    · exact allRGS_spec 6 0 _ h6 c e hc
    · exact allRGS_spec 7 0 _ h7 c e hc
  have h := allBelow_spec 7 _ hz s0 hs0
  rcases Bool.or_eq_true_iff.1 h with h0 | hm
  · unfold rowOK6
    rw [h0]
    rfl
  · obtain ⟨i, hi⟩ := hr (c, s0) (of_decide_eq_true hm)
    exact rowOK6_mono T (fun k hk => mem_flatten_getD hk) hi

/-! ## The H8 table -/

/-- Shape of the H8 keys: 8 directions and 6 counts, all digits below 9. -/
def keysOKH8 (hkeys : List (List Nat × List Nat)) : Bool :=
  hkeys.all (fun k => k.1.length == 8 && k.2.length == 6 && k.1.all (· < 9) && k.2.all (· < 9))

/-- The H8 tree holds exactly the codes of the H8 keys (in order). -/
def CoverH8 (T : Tables6S) (hkeys : List (List Nat × List Nat)) : Prop :=
  T.htree.toList = hkeys.map (fun k => encB 9 (k.1 ++ k.2) 0)

def coverH8b (T : Tables6S) (hkeys : List (List Nat × List Nat)) : Bool :=
  T.htree.toList == hkeys.map (fun k => encB 9 (k.1 ++ k.2) 0)

theorem coverH8_of {T : Tables6S} {hkeys : List (List Nat × List Nat)} (h : coverH8b T hkeys = true) :
    CoverH8 T hkeys := by
  simpa [coverH8b] using h

/-- A hit of the H8 tree is an H8 key. -/
theorem coverH8_spec {T : Tables6S} {hkeys : List (List Nat × List Nat)} (hc : CoverH8 T hkeys)
    (hv : keysOKH8 hkeys = true) {ds syms : List Nat} (hl : ds.length = 8) (hsl : syms.length = 6)
    (hs : ∀ s ∈ syms, s ≤ 6) (hb : wforbH8 T ds syms = true) :
    (canon ds.reverse, syms.reverse) ∈ hkeys := by
  unfold wforbH8 at hb
  have hm := NTree.mem_toList _ _ hb
  rw [hc, List.mem_map] at hm
  obtain ⟨k, hk, he⟩ := hm
  have hkv := List.all_eq_true.1 hv _ hk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hkv
  obtain ⟨⟨⟨hk1, hk2⟩, hk3⟩, hk4⟩ := hkv
  have hcl : (canon ds.reverse).length = 8 := by rw [length_canon, List.length_reverse, hl]
  have hcd : ∀ x ∈ canon ds.reverse, x < 9 := by
    intro x hx
    have := isRGS_lt _ 0 (canon_isRGS _) x hx
    omega
  have hs' : ∀ s ∈ syms.reverse, s ≤ 6 := fun s h => hs s (List.mem_reverse.1 h)
  have heq := encB_inj 9 _ _ (by simp [hk1, hk2, hcl, hsl]) (by
      intro s hs
      rcases List.mem_append.1 hs with h | h
      · exact hk3 s h
      · exact hk4 s h) (by
      intro s hs
      rcases List.mem_append.1 hs with h | h
      · exact hcd s h
      · have := hs' s h
        omega) he
  obtain ⟨h1, h2⟩ := List.append_inj heq (by rw [hk1, hcl])
  rw [← h1, ← h2]
  exact hk

section Window
variable {m : Nat} (p : Snake m)

/-- An H8 key on the window of 8 directions at `r`, counted on its first six interior vertices,
contradicts its certificate. -/
theorem window_refuteH8 {hkeys : List (List Nat × List Nat)} (h : AllRefutedList hkeys)
    (r : Nat) (hr : r + 8 ≤ m)
    (hkey : (canon (dsOf p r 8), (symsOf p r 8).take 6) ∈ hkeys) : False := by
  have hlen := length_dsOf p r 8
  have href := AllRefutedList.mem h _ hkey
  have hmem : ∀ j, j < 8 → (dsOf p r 8).getD j 0 ∈ seenAfter [] (dsOf p r 8) := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  refine refuted_dirH href p r (u := seenAfter [] (dsOf p r 8))
    (by simp only [List.length_take, length_canon, length_symsOf, hlen]; omega)
    (by rw [length_canon]; omega)
    (seenAfter_nodup [] _ List.nodup_nil) ?_ ?_ ?_
  · intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  · intro j hj
    rw [length_canon] at hj
    have e : (canon (dsOf p r 8)).getD j 0 = idx (seenAfter [] (dsOf p r 8)) ((dsOf p r 8).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j (by omega)), ?_⟩
    rw [getD_idx _ _ (hmem j (by omega)), getD_dsOf p (by omega)]
  · intro i hi
    have hi6 : i < 6 := by simpa [length_symsOf] using hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi6, ← List.getD_eq_getElem?_getD]
    exact getD_symsOf p (by omega)

/-- No H8 window of a snake is excluded: directions `d(r..r+7)`, counts of the interior
vertices `r+2..r+7` (the vertex `r+1` uncounted). -/
theorem no_forb_H8 {T : Tables6S} {hkeys : List (List Nat × List Nat)} (h : AllRefutedList hkeys)
    (hv : keysOKH8 hkeys = true) (hc : CoverH8 T hkeys) (r : Nat) (hr : r + 8 ≤ m) :
    wforbH8 T (dsOf p r 8) ((symsOf p r 8).drop 1) = false := by
  cases hw : wforbH8 T (dsOf p r 8) ((symsOf p r 8).drop 1)
  · rfl
  · exfalso
    have hkey := coverH8_spec hc hv (length_dsOf p r 8) (by simp [length_symsOf]) (by
      intro s hs
      have hs' := List.mem_of_mem_drop hs
      simp only [symsOf, List.mem_map] at hs'
      obtain ⟨i, _, rfl⟩ := hs'
      exact symC_le_six _) hw
    rw [← dsOf_rev p r 8 hr, reverse_drop_one, length_symsOf, ← symsOf_rev p r 8 hr] at hkey
    exact window_refuteH8 (revSnake p) h (m - r - 8) (by omega) hkey

end Window

/-- The window premises `Windows6S` of `total_bound6S`, for the path directions and the core
singleton count, from the certificate statements of the k6 keys and of the H8 keys. -/
theorem direction_windows_core6S {T : Tables6S} {keys hkeys : List (List Nat × List Nat)}
    (h : AllRefutedList keys) (hv : keysOK6 keys = true) (hc : Cover6 T.k6 keys)
    (hh : AllRefutedList hkeys) (hvh : keysOKH8 hkeys = true) (hch : CoverH8 T hkeys)
    {m : Nat} (p : Snake m) : Windows6S T (pathDir p) (coreAlpha p) m := by
  refine ⟨direction_windows_core6 h hv hc p, fun j hj => ?_⟩
  have := no_forb_H8 p hh hvh hch j hj
  unfold win8s6
  rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
  exact this

end Snake9.DirectionWindow6S

#print axioms Snake9.DirectionWindow6S.shareOK_floor
#print axioms Snake9.DirectionWindow6S.shareCover_rows
#print axioms Snake9.DirectionWindow6S.share_window6
#print axioms Snake9.DirectionWindow6S.share_windows6S
#print axioms Snake9.DirectionWindow6S.cover6_chunks
#print axioms Snake9.DirectionWindow6S.no_forb_H8
#print axioms Snake9.DirectionWindow6S.direction_windows_core6S
