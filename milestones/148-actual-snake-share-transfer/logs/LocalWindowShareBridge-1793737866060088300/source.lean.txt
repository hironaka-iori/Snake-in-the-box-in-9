import LocalWindowShareModel
import LocalWindowDirBridge

/-!
# From a snake to the share certificates

Stage 1 of `milestones/11-local-ceiling/s0_lean_design.md` (§2.2).  The frame
`amap P t v = π(v ⊕ t)` of `LocalWindowBridge` maps squares to squares and
neighbourhoods to neighbourhoods, so every share quantity is frame-invariant:

* `emptyPred_frame`, `emptyCount_frame`, `cnt_nbrs_frame`, `shareLocal_frame`
  (copies of `singPred_frame`, `singCount_frame`, plus a reindexing of the nine
  coordinates by the permutation `P`);
* `coreShare M p k = shareLocal M (sel p id) (vx p k)` is the share of the snake's
  `k`-th vertex in the identity frame, and `shareSum_window` identifies the share sum
  of the canonical window's centres with `Σ_i coreShare M p (r+i+1)`;
* `frame_axiomsS` / `refuted_share_bridge`: a share certificate
  `RefutedShare W bounds M K` forces `K + 1 ≤ Σ_i coreShare M p (r+i+1)` on every
  snake window mapped onto `W`;
* `refuted_share_dir`: the same through the first-occurrence relabelling used by the
  direction certificates (copy of `refuted_dir`);
* `coreShare_rev`, `coreShare_window_rev`: the share of the reversed snake, and the
  share sum of a window read from the reversed snake (for the reversed lookup of
  stage 5's `share_window5`).

The identification `shareN M p (p.vertex k) = coreShare M p k` with the global share of
`work/spectral/ShareCharge.lean` needs mathlib (`Finset`, `AxisPair`) and belongs next
to `localAlpha_eq_coreAlpha` in `work/spectral/stronger/AggregateWindowUnconditional.lean`;
the core-side shapes it consumes are `coreShare_eq_sum` below together with
`emptyPred_iff`, `emptyCount_eq_zero_of_sel` and `cnt_nbrs_eq` of `LocalWindowShareModel`.
-/

namespace Snake9.LocalWindow
open Snake9

set_option maxHeartbeats 1000000

/-! ## Permutations and sums of lists (core Lean has no `perm_ext_iff_of_nodup`) -/

/-- A duplicate-free list contained in a list of no greater length is a permutation of it. -/
theorem perm_of_nodup_subset_length {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₂.length ≤ l₁.length → l₁.Perm l₂
  | [], l₂, _, _, hl => by
    have : l₂ = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
    subst this
    exact List.Perm.nil
  | a :: t, l₂, hn, hs, hl => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ l₂ := hs a List.mem_cons_self
    have h1 : t.Perm (l₂.erase a) := perm_of_nodup_subset_length hn.2 (by
        intro x hx
        have hxa : x ≠ a := fun h => hn.1 (h ▸ hx)
        exact (List.mem_erase_of_ne hxa).2 (hs x (List.mem_cons_of_mem _ hx)))
      (by
        rw [List.length_erase_of_mem ha]
        simp only [List.length_cons] at hl
        omega)
    exact (List.Perm.cons a h1).trans (List.perm_cons_erase ha).symm

theorem sum_of_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons, ih]
  | swap x y l => simp only [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `P.fwd` permutes the nine coordinates. -/
theorem range9_perm_fwd (P : CPerm) : ((List.range 9).map P.fwd).Perm (List.range 9) := by
  apply perm_of_nodup_subset_length
  · apply nodup_map_of_inj List.nodup_range
    intro a ha b hb h
    exact P.fwd_inj (List.mem_range.1 ha) (List.mem_range.1 hb) h
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (P.fwd_lt k (List.mem_range.1 hk))
  · simp

/-- Reindexing a sum over the nine coordinates by `P.fwd`. -/
theorem sum_range9_fwd (P : CPerm) (g : Nat → Nat) :
    ((List.range 9).map fun k => g (P.fwd k)).sum = ((List.range 9).map g).sum := by
  have h := sum_of_perm ((range9_perm_fwd P).map g)
  rw [List.map_map] at h
  exact h

/-! ## Frame invariance of the share -/

section Frame
variable {m : Nat} (p : Snake m) (P : CPerm) (t : Nat)

theorem emptyPred_frame (ht : t < 512) {q : Nat} (hq : q < 512) {a b : Nat} (ha : a < 9) (hb : b < 9) :
    emptyPred (sel p (amap P t)) (amap P t q) (P.fwd a, P.fwd b) =
      emptyPred (sel p (fun v => v)) q (a, b) := by
  unfold emptyPred
  simp only [Nat.one_shiftLeft]
  rw [← amap_flip P t q ha, ← amap_flip P t q hb, ← amap_flip P t _ hb,
    sel_amap p P t ht hq, sel_amap p P t ht (xor_pow_lt hq ha), sel_amap p P t ht (xor_pow_lt hq hb),
    sel_amap p P t ht (xor_pow_lt (xor_pow_lt hq ha) hb)]

theorem emptyPred_frame_sorted (ht : t < 512) {q : Nat} (hq : q < 512) {a b : Nat} (ha : a < 9) (hb : b < 9) :
    emptyPred (sel p (amap P t)) (amap P t q) (min (P.fwd a) (P.fwd b), max (P.fwd a) (P.fwd b)) =
      emptyPred (sel p (fun v => v)) q (a, b) := by
  rw [← emptyPred_frame p P t ht hq ha hb]
  by_cases h : P.fwd a ≤ P.fwd b
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega), emptyPred_symm]

/-- Empty-square counts are invariant under the frame (as `singCount_frame`). -/
theorem emptyCount_frame (ht : t < 512) {q : Nat} (hq : q < 512) :
    emptyCount (sel p (amap P t)) (amap P t q) = emptyCount (sel p (fun v => v)) q := by
  unfold emptyCount
  apply Nat.le_antisymm
  · apply filter_length_le _ (freePairs_nodup 9 (by omega) 9 (by omega)) _ _
      (sorted_mem_inj P.inv)
    rintro ⟨a, b⟩ hx hs
    refine ⟨sorted_mem P.inv _ hx, ?_⟩
    have hx' := (mem_freePairs a b 9 9).1 hx
    simp only [CPerm.inv]
    rw [emptyPred_sort, ← emptyPred_frame p P t ht hq (P.bwd_lt a (by omega)) (P.bwd_lt b hx'.2.1),
      P.fwd_bwd a (by omega), P.fwd_bwd b hx'.2.1]
    exact hs
  · apply filter_length_le _ (freePairs_nodup 9 (by omega) 9 (by omega)) _ _
      (sorted_mem_inj P)
    rintro ⟨a, b⟩ hx hs
    refine ⟨sorted_mem P _ hx, ?_⟩
    have hx' := (mem_freePairs a b 9 9).1 hx
    rw [emptyPred_frame_sorted p P t ht hq (by omega) hx'.2.1]
    exact hs

/-- Selected-neighbour counts are invariant under the frame. -/
theorem cnt_nbrs_frame (ht : t < 512) {q : Nat} (hq : q < 512) :
    cnt (sel p (amap P t)) (nbrs (amap P t q)) = cnt (sel p (fun v => v)) (nbrs q) := by
  rw [cnt_nbrs_eq, cnt_nbrs_eq]
  apply Nat.le_antisymm
  · refine filter_length_le (List.range 9) List.nodup_range (List.range 9) P.bwd ?_ _ _ ?_
    · intro a ha b hb h
      have := congrArg P.fwd h
      rwa [P.fwd_bwd a (List.mem_range.1 ha), P.fwd_bwd b (List.mem_range.1 hb)] at this
    · intro k hk hs
      have hk' := List.mem_range.1 hk
      have hb := P.bwd_lt k hk'
      refine ⟨List.mem_range.2 hb, ?_⟩
      show sel p (fun v => v) (q ^^^ 2 ^ P.bwd k) = true
      rw [← sel_amap p P t ht (xor_pow_lt hq hb), amap_flip P t q hb, P.fwd_bwd k hk']
      exact hs
  · refine filter_length_le (List.range 9) List.nodup_range (List.range 9) P.fwd ?_ _ _ ?_
    · intro a ha b hb h
      exact P.fwd_inj (List.mem_range.1 ha) (List.mem_range.1 hb) h
    · intro k hk hs
      have hk' := List.mem_range.1 hk
      refine ⟨List.mem_range.2 (P.fwd_lt k hk'), ?_⟩
      show sel p (amap P t) (amap P t q ^^^ 2 ^ P.fwd k) = true
      rw [← amap_flip P t q hk', sel_amap p P t ht (xor_pow_lt hq hk')]
      exact hs

/-- The local share is invariant under the frame. -/
theorem shareLocal_frame (ht : t < 512) {x : Nat} (hx : x < 512) (M : Nat) :
    shareLocal M (sel p (amap P t)) (amap P t x) = shareLocal M (sel p (fun v => v)) x := by
  rw [shareLocal_eq, shareLocal_eq, ← sum_range9_fwd P]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.1 hk
  show M * emptyCount (sel p (amap P t)) (amap P t x ^^^ 2 ^ P.fwd k) /
      cnt (sel p (amap P t)) (nbrs (amap P t x ^^^ 2 ^ P.fwd k)) =
    M * emptyCount (sel p (fun v => v)) (x ^^^ 2 ^ k) / cnt (sel p (fun v => v)) (nbrs (x ^^^ 2 ^ k))
  rw [← amap_flip P t x hk', emptyCount_frame p P t ht (xor_pow_lt hx hk'),
    cnt_nbrs_frame p P t ht (xor_pow_lt hx hk')]

end Frame

/-! ## The share of a snake vertex -/

/-- The corner share of the snake's `k`-th vertex (identity frame; as `coreAlpha`). -/
def coreShare {m : Nat} (M : Nat) (p : Snake m) (k : Nat) : Nat :=
  shareLocal M (sel p (fun v => v)) (vx p k)

/-- `coreShare` as the nine-term sum over the neighbours `vx p k ⊕ e_j`: the shape of
`shareN M p (p.vertex k) = Σ_{j : Fin 9} M · emptyAt(flip j x) / selDeg(flip j x)`, with
`emptyAt ↔ emptyCount` (`emptyPred_iff`, bijection `AxisPair ↔ freePairs 9 9`) and
`selDeg ↔ cnt S (nbrs ·)` (`cnt_nbrs_eq`) still to be supplied on the mathlib side. -/
theorem coreShare_eq_sum {m : Nat} (M : Nat) (p : Snake m) (k : Nat) :
    coreShare M p k = ((List.range 9).map fun j =>
      M * emptyCount (sel p (fun v => v)) (vx p k ^^^ 2 ^ j) /
        cnt (sel p (fun v => v)) (nbrs (vx p k ^^^ 2 ^ j))).sum :=
  shareLocal_eq M _ _

/-! ## The bridge -/

section Bridge
variable {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)

/-- The share sum of the canonical window's centres is the sum of the snake's shares
at the window's interior vertices. -/
theorem shareSum_window {W cs : List Nat} {bounds : List (Nat × Nat)} (hc : Canon W cs)
    (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0) (M : Nat) :
    shareSum M (sel p (amap P (vx p r))) (centresOf W bounds) =
      ((List.range bounds.length).map fun i => coreShare M p (r + i + 1)).sum := by
  unfold shareSum centresOf
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  show shareLocal M (sel p (amap P (vx p r))) (W.getD (i + 1) 0) = coreShare M p (r + i + 1)
  rw [frame_window p P r hc hr hP (i + 1) (by omega)]
  exact shareLocal_frame p P _ (vx_lt p r) (vx_lt p _) M

/-- The image of a snake around a window satisfies the share axioms with the cap equal
to its own share sum. -/
theorem frame_axiomsS {W cs : List Nat} {bounds : List (Nat × Nat)} (hc : Canon W cs)
    (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0)
    (hb : ∀ i, i < bounds.length → (bounds.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (bounds.getD i (0, 21)).2) (M : Nat) :
    AxiomsS (sel p (amap P (vx p r))) (frameE p P (vx p r)) W (centresOf W bounds) M
      (((List.range bounds.length).map fun i => coreShare M p (r + i + 1)).sum) :=
  ⟨frame_axioms p P r hc hlen hr hP hb, Nat.le_of_eq (shareSum_window p P r hc hlen hr hP M)⟩

/-- A share certificate with cap `K` forces the share sum above `K` on every window of a
snake whose directions are mapped onto the canonical ones by `P`. -/
theorem refuted_share_bridge {W cs : List Nat} {bounds : List (Nat × Nat)} {M K : Nat}
    (href : RefutedShare W bounds M K)
    (hc : Canon W cs) (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0)
    (hb : ∀ i, i < bounds.length → (bounds.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (bounds.getD i (0, 21)).2) :
    K + 1 ≤ ((List.range bounds.length).map fun i => coreShare M p (r + i + 1)).sum := by
  apply Nat.succ_le_of_lt
  apply Nat.lt_of_not_le
  intro hle
  exact href _ _ ((frame_axiomsS p P r hc hlen hr hP hb M).mono hle)

end Bridge

/-- A share certificate keyed by a direction list and lumped counts (as `refuted_dir`):
on every snake window relabelled onto `cs` by the duplicate-free coordinate list `u`
and with the lumped counts `syms`, the share sum exceeds the cap. -/
theorem refuted_share_dir {cs syms u : List Nat} {M K : Nat}
    (h : RefutedShare (winOf cs) (boundsOf syms) M K)
    {m : Nat} (p : Snake m) (r : Nat) (hlen : syms.length + 1 = cs.length)
    (hr : r + cs.length ≤ m) (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j, j < cs.length → cs.getD j 0 < u.length ∧ u.getD (cs.getD j 0) 0 = dir p (r + j))
    (hs : ∀ i, i < syms.length → syms.getD i 0 = symC (coreAlpha p (r + i + 1))) :
    K + 1 ≤ ((List.range syms.length).map fun i => coreShare M p (r + i + 1)).sum := by
  have hlen9 : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hsp := mkPerm_spec hu hu9 hlen9
  have hres := refuted_share_bridge p (mkPerm u) r h (canon_winOf cs) (by simp [boundsOf, hlen]) hr
    (by
      intro j hj
      obtain ⟨h1, h2⟩ := hcs j hj
      rw [← h2]
      exact hsp _ h1)
    (by
      intro i hi
      have hi' : i < syms.length := by simpa [boundsOf] using hi
      rw [getD_boundsOf hi', hs i hi']
      exact boundOf_symC (coreAlpha_le_21 p (by omega) (by omega)))
  have e : (boundsOf syms).length = syms.length := List.length_map _
  rw [e] at hres
  exact hres

/-! ## Reversal -/

theorem coreShare_rev {m : Nat} (M : Nat) (p : Snake m) {k : Nat} (hk : k ≤ m) :
    coreShare M (revSnake p) k = coreShare M p (m - k) := by
  unfold coreShare
  rw [sel_rev, vx_rev p hk]

/-- `i ↦ n - 1 - i` permutes `range n`. -/
theorem range_rev_perm (n : Nat) : ((List.range n).map fun i => n - 1 - i).Perm (List.range n) := by
  apply perm_of_nodup_subset_length
  · apply nodup_map_of_inj List.nodup_range
    intro a ha b hb h
    have := List.mem_range.1 ha
    have := List.mem_range.1 hb
    omega
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 hk
    exact List.mem_range.2 (by omega)
  · simp

theorem sum_range_rev (f : Nat → Nat) (n : Nat) :
    ((List.range n).map fun i => f (n - 1 - i)).sum = ((List.range n).map f).sum := by
  have h := sum_of_perm ((range_rev_perm n).map f)
  rw [List.map_map] at h
  exact h

/-- The window of `c` centres starting at `r` and its image in the reversed snake
(starting at `m - r - c - 1`) have the same share sum: the centres are the same
vertices in the opposite order. -/
theorem coreShare_window_rev {m : Nat} (M : Nat) (p : Snake m) (r c : Nat) (hr : r + c + 1 ≤ m) :
    ((List.range c).map fun i => coreShare M (revSnake p) (m - r - c - 1 + i + 1)).sum =
      ((List.range c).map fun i => coreShare M p (r + i + 1)).sum := by
  rw [← sum_range_rev (fun i => coreShare M p (r + i + 1)) c]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  show coreShare M (revSnake p) (m - r - c - 1 + i + 1) = coreShare M p (r + (c - 1 - i) + 1)
  rw [coreShare_rev M p (by omega)]
  congr 1
  omega

#print axioms refuted_share_bridge
#print axioms refuted_share_dir

end Snake9.LocalWindow
