module

public import C230Shapes
public import C230Shares
public import AggregateDirectionK7R34C7W16Conditional
public import ShareBridge

@[expose] public section

/-!
# The bound 230 from the K7 chain, the window table and the corner-share floor (milestone 37)

* **Walk** (`walk230`): the chain `total_boundK7R34C7W16` with `d = pathDir p`, `a = coreAlpha p` and
  the premises `hw2 .. hw7` from `C230K7.no_forb` (key table `tab230`, shape covers and row checks of
  `C230Shapes`):  `89 m ≤ 19 Σ_{k=1}^{m-1} α_k + 678`.
* **Shares** (`window_share`): every 8-direction window `j` (`j + 8 ≤ m`) has a canonical shape in
  `shapes8 = shares230`, whose certificate `RefutedShare (winOf s) [(1,21)] x 7 12 29` gives corner share
  (`coreShare 12`) at least 30 on its 7 centres (`LocalWindowShareBridge.refuted_share_bridge`).
  A vertex is a centre of at most 7 of the `m - 7` windows `j = 0 .. m-8`.
* **Count** (`ShareBridge.core_charge_sum_le 12`): `Σ_{k ≤ m} (24 α_k + share_k) + 840 (m + 1) ≤ 221136`,
  with `α_0, α_m ≥ 4`. Together: `127242 m ≤ 29391726`, so `m ≤ 230`.

`upper_230_of_tables` takes the two certificate premises `AllTab tab230` and `AllShareL shares230`
(the glue: `G230.allTab230`, `G230.allShare230`).
-/

namespace Snake9.C230
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow Finset

/-! ## The walk inequality -/

section Walk
variable {m : Nat} (p : Snake m)

theorem dsOf_eq_blockList {r n : Nat} (hr : r + n ≤ m) : dsOf p r n = blockList p r n := by
  apply List.ext_getElem
  · simp [blockList, dsOf]
  · intro j h1 h2
    simp only [blockList, dsOf, List.getElem_map, List.getElem_range', List.getElem_range, Nat.one_mul]
    simp only [dsOf, List.length_map, List.length_range] at h1
    exact (pathDir_eq_dir p (by omega)).symm

theorem coreAlpha_pos (hm : 3 ≤ m) : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ coreAlpha p j := by
  obtain ⟨_, _, hpos, _, _⟩ := countSeq_facts p hm
  intro j hj hjm
  have := hpos (j - 1) (by omega)
  rwa [show j - 1 + 1 = j by omega, countSeq_eq_coreAlpha_le p j (by omega)] at this

theorem no_forb230 (hT : AllTab tab230) (hm : 3 ≤ m) (n : Nat) (hn : 3 ≤ n ∧ n ≤ 8) (r : Nat) (hr : r + n ≤ m) :
    wforbK7R34C7W16 (blockList p r n) (symsK p r n) = false := by
  rw [← dsOf_eq_blockList p hr]
  have hpos := coreAlpha_pos p hm
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_forb p hT hn cover3 good3 hpos r hr
  · exact no_forb p hT hn cover4 good4 hpos r hr
  · exact no_forb p hT hn cover5 good5 hpos r hr
  · exact no_forb p hT hn cover6 good6 hpos r hr
  · exact no_forb p hT hn cover7 good7 hpos r hr
  · exact no_forb p hT hn cover8 good8 hpos r hr

theorem walk230 (hT : AllTab tab230) (hm : 8 ≤ m) :
    89 * m ≤ 19 * sumA (coreAlpha p) (m - 1) + 678 :=
  total_boundK7R34C7W16 (pathDir p) (coreAlpha p) m hm (coreAlpha_pos p (by omega))
    (fun i hi => by rw [winK7R34C7W16_eq]; exact snake_inducedPattern_block p i 9 hi)
    (fun j hj => no_forb230 p hT (by omega) 3 (by omega) j hj)
    (fun j hj => no_forb230 p hT (by omega) 4 (by omega) j hj)
    (fun j hj => no_forb230 p hT (by omega) 5 (by omega) j hj)
    (fun j hj => no_forb230 p hT (by omega) 6 (by omega) j hj)
    (fun j hj => no_forb230 p hT (by omega) 7 (by omega) j hj)
    (fun j hj => no_forb230 p hT (by omega) 8 (by omega) j hj)

/-! ## Window shares -/

/-- `LocalWindowShareBridge.refuted_share_dir` with explicit interval bounds. -/
theorem refuted_share_dir_iv {cs u : List Nat} {b : List (Nat × Nat)} {M K : Nat}
    (h : RefutedShare (winOf cs) b M K) (r : Nat) (hlen : b.length + 1 = cs.length)
    (hr : r + cs.length ≤ m) (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j, j < cs.length → cs.getD j 0 < u.length ∧ u.getD (cs.getD j 0) 0 = dir p (r + j))
    (hb : ∀ i, i < b.length → (b.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (b.getD i (0, 21)).2) :
    K + 1 ≤ ((List.range b.length).map fun i => coreShare M p (r + i + 1)).sum := by
  have hlen9 : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hsp := mkPerm_spec hu hu9 hlen9
  refine refuted_share_bridge p (mkPerm u) r h (canon_winOf cs) hlen hr ?_ hb
  intro j hj
  obtain ⟨h1, h2⟩ := hcs j hj
  rw [← h2]
  exact hsp _ h1

def free7 : List (Nat × Nat) := [(1, 21), (1, 21), (1, 21), (1, 21), (1, 21), (1, 21), (1, 21)]

theorem window_share (hS : AllShareL shares230) (hm : 3 ≤ m) (j : Nat) (hj : j + 8 ≤ m) :
    30 ≤ ∑ i ∈ range 7, coreShare 12 p (j + i + 1) := by
  have hpos := coreAlpha_pos p hm
  have hsh : canon (dsOf p j 8) ∈ shares230 := by
    rw [dsOf_eq_blockList p hj, show shares230 = shapes8 from rfl]
    exact window_shape_mem (by decide) cover8 p j hj
  have href := hS.mem _ hsh
  have hlen := length_dsOf p j 8
  have hmem : ∀ k, k < 8 → (dsOf p j 8).getD k 0 ∈ seenAfter [] (dsOf p j 8) := by
    intro k hk
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have h := refuted_share_dir_iv p href j (u := seenAfter [] (dsOf p j 8)) (by rw [length_canon]; omega)
    (by rw [length_canon]; omega) (seenAfter_nodup [] _ List.nodup_nil) ?_ ?_ ?_
  · rw [← List.sum_range_succ_comm] at h
    simpa [List.sum_range_succ, Finset.sum_range_succ] using h
  · intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨k, hk, rfl⟩ := h
      exact dir_lt p (by omega)
  · intro k hk
    rw [length_canon] at hk
    have e : (canon (dsOf p j 8)).getD k 0 = idx (seenAfter [] (dsOf p j 8)) ((dsOf p j 8).getD k 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem k (by omega)), ?_⟩
    rw [getD_idx _ _ (hmem k (by omega)), getD_dsOf p (by omega)]
  · intro i hi
    have hi7 : i < 7 := by simpa using hi
    have e : ([(1, 21), (1, 21), (1, 21), (1, 21), (1, 21), (1, 21), (1, 21)] : List (Nat × Nat)).getD i (0, 21) = (1, 21) := by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e]
    exact ⟨hpos _ (by omega) (by omega), coreAlpha_le_21 p (by omega) (by omega)⟩

/-- A shifted range sum is at most the full sum. -/
theorem shift_sum_le (f : Nat → Nat) (c N M : Nat) (h : c + N ≤ M) :
    ∑ j ∈ range N, f (j + c) ≤ ∑ k ∈ range M, f k := by
  have e := Finset.sum_range_add f c N
  have hs : ∑ k ∈ range (c + N), f k ≤ ∑ k ∈ range M, f k :=
    Finset.sum_le_sum_of_subset (Finset.range_subset.2 h)
  have : ∑ j ∈ range N, f (j + c) = ∑ x ∈ range N, f (c + x) := by
    apply Finset.sum_congr rfl; intro x _; rw [Nat.add_comm]
  omega

theorem sum_windows_le (hm : 8 ≤ m) :
    ∑ j ∈ range (m - 7), ∑ i ∈ range 7, coreShare 12 p (j + i + 1) ≤
      7 * ∑ k ∈ range (m + 1), coreShare 12 p k := by
  rw [Finset.sum_comm]
  have : ∀ i ∈ range 7, ∑ j ∈ range (m - 7), coreShare 12 p (j + i + 1) ≤ ∑ k ∈ range (m + 1), coreShare 12 p k := by
    intro i hi
    rw [Finset.mem_range] at hi
    have := shift_sum_le (coreShare 12 p) (i + 1) (m - 7) (m + 1) (by omega)
    simpa [Nat.add_assoc] using this
  calc ∑ i ∈ range 7, ∑ j ∈ range (m - 7), coreShare 12 p (j + i + 1)
      ≤ ∑ _i ∈ range 7, ∑ k ∈ range (m + 1), coreShare 12 p k := Finset.sum_le_sum this
    _ = 7 * ∑ k ∈ range (m + 1), coreShare 12 p k := by simp

/-! ## The count -/

theorem psum_eq_sum (h : Nat → Nat) : ∀ n, psum h n = ∑ k ∈ range n, h k
  | 0 => rfl
  | n + 1 => by rw [psum, psum_eq_sum h n, Finset.sum_range_succ]

theorem alpha_split (hm : 1 ≤ m) : ∑ k ∈ range (m + 1), coreAlpha p k =
    coreAlpha p 0 + sumA (coreAlpha p) (m - 1) + coreAlpha p m := by
  rw [sumA_eq_psum, psum_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ']
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  omega

theorem upper_230_of_tables (hT : AllTab tab230) (hS : AllShareL shares230) : m ≤ 230 := by
  by_cases hm : m < 9
  · omega
  have hwalk := walk230 p hT (by omega)
  obtain ⟨h0, h1, _, _, _⟩ := countSeq_facts p (by omega)
  rw [countSeq_eq_coreAlpha_le p 0 (by omega)] at h0
  rw [countSeq_eq_coreAlpha_le p m (by omega)] at h1
  have hid := core_charge_sum_le 12 p (by omega)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, alpha_split p (by omega)] at hid
  have hw : 30 * (m - 7) ≤ ∑ j ∈ range (m - 7), ∑ i ∈ range 7, coreShare 12 p (j + i + 1) := by
    have := Finset.card_nsmul_le_sum (range (m - 7)) (fun j => ∑ i ∈ range 7, coreShare 12 p (j + i + 1)) 30
      (fun j hj => window_share p hS (by omega) j (by rw [Finset.mem_range] at hj; omega))
    simpa [mul_comm] using this
  have hsw := sum_windows_le p (by omega)
  omega

end Walk

end Snake9.C230

namespace Snake9

/-- The bound 230 from the two certificate premises of the K7 route. -/
theorem upper_230_of_refutedK7 (hT : C230.AllTab C230.tab230) (hS : C230.AllShareL C230.shares230) :
    ∀ {m : Nat}, Snake m → m ≤ 230 :=
  fun p => C230.upper_230_of_tables p hT hS

end Snake9
