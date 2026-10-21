import ParallelShareModel
import LocalWindowShareBridge

/-! Translation, coordinate permutation and reversal for the parallel-square
share. The older corner-share theorem is not used to identify this quantity. -/
namespace Snake9.LocalWindow
open Snake9
set_option maxHeartbeats 1000000

def mappedPair (P : CPerm) (ab : Nat × Nat) : Nat × Nat :=
  (min (P.fwd ab.1) (P.fwd ab.2), max (P.fwd ab.1) (P.fwd ab.2))

theorem pairs_perm_fwd (P : CPerm) :
    ((freePairs 9 9).map (mappedPair P)).Perm (freePairs 9 9) := by
  apply perm_of_nodup_subset_length
  · apply nodup_map_of_inj (freePairs_nodup 9 (by omega) 9 (by omega))
    exact sorted_mem_inj P
  · intro x hx
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.1 hx
    exact sorted_mem P ab hab
  · simp

section Frame
variable {m : Nat} (p : Snake m) (P : CPerm) (t : Nat)

theorem parallelCount_frame (ht : t < 512) {v : Nat} (hv : v < 512)
    {a b : Nat} (ha : a < 9) (hb : b < 9) :
    parallelCount (sel p (amap P t)) (amap P t v) (P.fwd a, P.fwd b) =
      parallelCount (sel p (fun v => v)) v (a, b) := by
  unfold parallelCount
  simp only
  rw [← amap_flip P t v ha, ← amap_flip P t v hb, ← amap_flip P t _ hb,
    sel_amap p P t ht hv, sel_amap p P t ht (xor_pow_lt hv ha),
    sel_amap p P t ht (xor_pow_lt hv hb),
    sel_amap p P t ht (xor_pow_lt (xor_pow_lt hv ha) hb)]

theorem parallelTerm_frame (ht : t < 512) {v : Nat} (hv : v < 512)
    {k a b : Nat} (hk : k < 9) (ha : a < 9) (hb : b < 9) :
    parallelTerm (sel p (amap P t)) (amap P t v) (P.fwd k) (P.fwd a, P.fwd b) =
      parallelTerm (sel p (fun v => v)) v k (a, b) := by
  have hea : P.fwd k ≠ P.fwd a ↔ k ≠ a :=
    ⟨fun h e => h (congrArg P.fwd e), fun h e => h (P.fwd_inj hk ha e)⟩
  have heb : P.fwd k ≠ P.fwd b ↔ k ≠ b :=
    ⟨fun h e => h (congrArg P.fwd e), fun h e => h (P.fwd_inj hk hb e)⟩
  unfold parallelTerm
  simp only [hea, heb]
  rw [← amap_flip P t v hk,
    emptyPred_frame p P t ht (xor_pow_lt hv hk) ha hb,
    parallelCount_frame p P t ht hv ha hb]

theorem parallelTerm_frame_sorted (ht : t < 512) {v : Nat} (hv : v < 512)
    {k a b : Nat} (hk : k < 9) (ha : a < 9) (hb : b < 9) :
    parallelTerm (sel p (amap P t)) (amap P t v) (P.fwd k) (mappedPair P (a, b)) =
      parallelTerm (sel p (fun v => v)) v k (a, b) := by
  unfold mappedPair
  rw [parallelTerm_sort, parallelTerm_frame p P t ht hv hk ha hb]

/-- The full parallel-share sum is invariant under every cube frame. -/
theorem parallelShare_frame (ht : t < 512) {v : Nat} (hv : v < 512) :
    parallelShare (sel p (amap P t)) (amap P t v) =
      parallelShare (sel p (fun v => v)) v := by
  unfold parallelShare
  rw [← sum_range9_fwd P]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.1 hk
  have hp := sum_of_perm ((pairs_perm_fwd P).map
    (fun ab => parallelTerm (sel p (amap P t)) (amap P t v) (P.fwd k) ab))
  rw [List.map_map] at hp
  rw [← hp]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨a, b⟩ hab
  have hab' := (mem_freePairs a b 9 9).1 hab
  exact parallelTerm_frame_sorted p P t ht hv hk' (by omega) hab'.2.1

end Frame

def coreParallelShare {m : Nat} (p : Snake m) (k : Nat) : Nat :=
  parallelShare (sel p (fun v => v)) (vx p k)

section Bridge
variable {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)

theorem parallelSum_window {W cs : List Nat} {bounds : List (Nat × Nat)} (hc : Canon W cs)
    (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0) :
    parallelSum (sel p (amap P (vx p r))) (centresOf W bounds) =
      ((List.range bounds.length).map fun i => coreParallelShare p (r + i + 1)).sum := by
  unfold parallelSum centresOf
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  show parallelShare (sel p (amap P (vx p r))) (W.getD (i + 1) 0) =
    coreParallelShare p (r + i + 1)
  rw [frame_window p P r hc hr hP (i + 1) (by omega)]
  exact parallelShare_frame p P _ (vx_lt p r) (vx_lt p _)

theorem frame_axiomsP {W cs : List Nat} {bounds : List (Nat × Nat)} (hc : Canon W cs)
    (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0)
    (hb : ∀ i, i < bounds.length → (bounds.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (bounds.getD i (0, 21)).2) :
    AxiomsP (sel p (amap P (vx p r))) (frameE p P (vx p r)) W (centresOf W bounds)
      (((List.range bounds.length).map fun i => coreParallelShare p (r + i + 1)).sum) :=
  ⟨frame_axioms p P r hc hlen hr hP hb,
    Nat.le_of_eq (parallelSum_window p P r hc hlen hr hP)⟩

/-- A local refutation yields the share bound for every snake window mapped to
the corresponding canonical shape, with no assumption about a snake bank. -/
theorem refuted_parallel_bridge {W cs : List Nat} {bounds : List (Nat × Nat)} {cap : Nat}
    (href : RefutedParallel W bounds cap)
    (hc : Canon W cs) (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0)
    (hb : ∀ i, i < bounds.length → (bounds.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (bounds.getD i (0, 21)).2) :
    cap + 1 ≤ ((List.range bounds.length).map fun i => coreParallelShare p (r + i + 1)).sum := by
  apply Nat.succ_le_of_lt
  apply Nat.lt_of_not_le
  intro hle
  exact href _ _ ((frame_axiomsP p P r hc hlen hr hP hb).mono hle)

end Bridge

/-- Share-only certificates use the unrestricted singleton bounds [0,21].
Their canonical coordinate list can be instantiated on any snake window. -/
theorem refuted_parallel_shape {cs u : List Nat} {cap : Nat}
    (href : RefutedParallel (winOf cs) (List.replicate (cs.length - 1) (0, 21)) cap)
    {m : Nat} (p : Snake m) (r : Nat) (hcspos : 1 ≤ cs.length)
    (hr : r + cs.length ≤ m) (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j, j < cs.length → cs.getD j 0 < u.length ∧
      u.getD (cs.getD j 0) 0 = dir p (r + j)) :
    cap + 1 ≤ ((List.range (cs.length - 1)).map fun i => coreParallelShare p (r + i + 1)).sum := by
  have huLen : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hperm := mkPerm_spec hu hu9 huLen
  have hbound := refuted_parallel_bridge p (mkPerm u) r href (canon_winOf cs)
    (by simp; omega) hr (by
      intro j hj
      obtain ⟨hj', he⟩ := hcs j hj
      rw [← he]
      exact hperm _ hj') (by
      intro i hi
      have hi' : i < cs.length - 1 := by simpa using hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi', ↓reduceIte,
        Option.getD_some]
      exact ⟨Nat.zero_le _, coreAlpha_le_21 p (by omega) (by omega)⟩)
  simpa only [List.length_replicate] using hbound

theorem coreParallelShare_rev {m : Nat} (p : Snake m) {k : Nat} (hk : k ≤ m) :
    coreParallelShare (revSnake p) k = coreParallelShare p (m - k) := by
  unfold coreParallelShare
  rw [sel_rev, vx_rev p hk]

theorem parallel_window_rev {m : Nat} (p : Snake m) (r c : Nat) (hr : r + c + 1 ≤ m) :
    ((List.range c).map fun i => coreParallelShare (revSnake p) (m - r - c - 1 + i + 1)).sum =
      ((List.range c).map fun i => coreParallelShare p (r + i + 1)).sum := by
  rw [← sum_range_rev (fun i => coreParallelShare p (r + i + 1)) c]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  show coreParallelShare (revSnake p) (m - r - c - 1 + i + 1) =
    coreParallelShare p (r + (c - 1 - i) + 1)
  rw [coreParallelShare_rev p (by omega)]
  apply congrArg (coreParallelShare p)
  omega

#print axioms parallelShare_frame
#print axioms frame_axiomsP
#print axioms refuted_parallel_bridge
#print axioms refuted_parallel_shape
#print axioms parallel_window_rev
end Snake9.LocalWindow
