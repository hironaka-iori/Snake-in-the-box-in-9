import Sh235Win
import WindowAutomatonLemmas
/-!
# Normalising an arbitrary window to its canonical shape; reversed snakes

* `dl p j L`: the `L` edge directions of `p` from position `j`.
* `norm_canon`: some cube automorphism image `q` of `p` runs through the window `wv (canon ds)`
  from position `j` (`ds = dl p j L`), with the same count sequence.  The coordinate
  permutation sends the `i`-th distinct direction of `ds` (in order of first appearance) to `i`,
  which is exactly the relabelling `canon` performs.
* `revS p`: the snake read backwards; it has the same vertex set, hence the same local counts
  read backwards, and its directions are those of `p` reversed.
-/
namespace S235
open Snake9 Snake9.SquareIncidence Snake9.WindowAutomaton Snake9.CubePerm

/-! ### `seenAfter` and `idx` -/

theorem seenAfter_nodup : ∀ (seen ds : List Nat), seen.Nodup → (seenAfter seen ds).Nodup
  | seen, [], h => h
  | seen, d :: ds, h => by
    unfold seenAfter
    split
    · exact seenAfter_nodup _ ds h
    · rename_i hd
      apply seenAfter_nodup
      exact List.nodup_append.mpr ⟨h, List.nodup_singleton d, by
        intro a ha hb; simp only [List.mem_singleton] at hb; subst hb; exact hd ha⟩

theorem mem_seenAfter_sub : ∀ (seen ds : List Nat) (x : Nat), x ∈ seenAfter seen ds → x ∈ seen ∨ x ∈ ds
  | seen, [], x, h => Or.inl h
  | seen, d :: ds, x, h => by
    unfold seenAfter at h
    split at h
    · rcases mem_seenAfter_sub _ ds x h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases mem_seenAfter_sub _ ds x h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · simp only [List.mem_singleton] at h; subst h; exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem getElem_idx : ∀ (l : List Nat) (d : Nat) (h : d ∈ l), l[idx l d]'(idx_lt_of_mem l d h) = d
  | [], d, h => absurd h List.not_mem_nil
  | a :: l, d, h => by
    by_cases had : a = d
    · subst had; simp [idx]
    · have h' : d ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm had
        · exact h
      have e : idx (a :: l) d = idx l d + 1 := by simp [idx, had]
      simp only [e, List.getElem_cons_succ]
      exact getElem_idx l d h'

/-! ### Directions of a window -/

def dl {m : Nat} (p : Snake m) (j L : Nat) : List Nat := (List.range L).map fun i => pathDir p (j + i)

theorem dl_length {m : Nat} (p : Snake m) (j L : Nat) : (dl p j L).length = L := by simp [dl]

theorem dl_getD {m : Nat} (p : Snake m) (j L i : Nat) (hi : i < L) : (dl p j L).getD i 0 = pathDir p (j + i) := by
  simp [dl, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem canon_getD (ds : List Nat) (i : Nat) (hi : i < ds.length) :
    (canon ds).getD i 0 = label ds (ds.getD i 0) := by
  rw [canon_eq_map]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem canon_length' (ds : List Nat) : (canon ds).length = ds.length := length_canon ds

/-- Normalisation along the canonical shape. -/
theorem norm_canon {m : Nat} (p : Snake m) (j L : Nat) (hj : j + L ≤ m) :
    ∃ q : Snake m, (∀ i ≤ L, vtx q (j + i) = wv (canon (dl p j L)) i) ∧
      ∀ k, countSeq q k = countSeq p k := by
  let ds := dl p j L
  let S := seenAfter [] ds
  have hS : S.Nodup := seenAfter_nodup [] ds List.nodup_nil
  have hS9 : ∀ x ∈ S, x < 9 := by
    intro x hx
    rcases mem_seenAfter_sub [] ds x hx with h | h
    · exact absurd h List.not_mem_nil
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
      exact pathDir_lt p _
  have hnd : (S.map coordOf).Nodup := by
    refine List.Nodup.map_on ?_ hS
    intro a ha b hb e
    have := congrArg Fin.val e
    simp only [coordOf, Nat.mod_eq_of_lt (hS9 a ha), Nat.mod_eq_of_lt (hS9 b hb)] at this
    exact this
  obtain ⟨σ, hσ⟩ := exists_perm_relabel _ hnd
  let q := cubeMap σ (p.vertex ⟨j, by omega⟩) p
  have hdir : ∀ i < L, pathDir q (j + i) = (canon ds).getD i 0 := by
    intro i hi
    rw [pathDir_cubeMap σ _ p _ (by omega)]
    have hmem : pathDir p (j + i) ∈ ds := List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    have hmS : pathDir p (j + i) ∈ S := mem_seenAfter [] ds _ hmem
    have hk := idx_lt_of_mem S _ hmS
    have h1 := hσ (idx S (pathDir p (j + i))) (by simpa using hk)
    simp only [List.getElem_map] at h1
    rw [getElem_idx S _ hmS] at h1
    have e : (⟨pathDir p (j + i), pathDir_lt p _⟩ : Coord) = coordOf (pathDir p (j + i)) := by
      apply Fin.ext; simp [coordOf, Nat.mod_eq_of_lt (pathDir_lt p _)]
    rw [e, h1, canon_getD ds i (by simp [ds, dl_length]; exact hi), dl_getD p j L i hi]
    rfl
  refine ⟨q, ?_, fun k => countSeq_cubeMap σ _ p k⟩
  intro i hi
  induction i with
  | zero =>
    rw [vtx_eq q (by omega)]
    simp only [Nat.add_zero, wv]
    show (cubeAut σ (p.vertex ⟨j, by omega⟩) (p.vertex ⟨j, by omega⟩)).val = 0
    unfold cubeAut; rw [vxor_self, permV_zero]; rfl
  | succ i ih =>
    have ih := ih (by omega)
    rw [vtx_eq q (by omega)] at ih ⊢
    show (q.vertex ⟨(j + i) + 1, by omega⟩).val = _
    rw [vertex_succ_eq q (j + i) (by omega), wv_succ, ← ih]
    show _ ^^^ 2 ^ pathDir q (j + i) = _
    rw [hdir i (by omega)]

/-! ### Reversed snakes -/

def revS {m : Nat} (p : Snake m) : Snake m where
  vertex i := p.vertex (Fin.rev i)
  distinct i j h := Fin.rev_injective (p.distinct _ _ h)
  induced i j hij := by
    have h := p.induced (Fin.rev j) (Fin.rev i) (by simp [Fin.val_rev]; omega)
    constructor
    · intro ha
      have := h.mp (adj_symmetric ha)
      simp [Fin.val_rev] at this; omega
    · intro he
      apply adj_symmetric
      apply h.mpr
      simp [Fin.val_rev]; omega

theorem inPath_revS {m : Nat} (p : Snake m) (v : Vertex) : InPath (revS p) v ↔ InPath p v := by
  constructor
  · rintro ⟨i, hi⟩; exact ⟨Fin.rev i, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨Fin.rev i, by show p.vertex (Fin.rev (Fin.rev i)) = v; rw [Fin.rev_rev]; exact hi⟩

open Classical in
theorem localAlpha_revS {m : Nat} (p : Snake m) (i : Fin (m+1)) :
    localAlpha (revS p) i = localAlpha p (Fin.rev i) := by
  unfold localAlpha
  apply Finset.sum_congr rfl
  intro ab _
  unfold SquareIncidence.singleton
  simp only [inPath_revS]
  rfl

theorem countSeq_revS {m : Nat} (p : Snake m) (k : Nat) (hk : k ≤ m) :
    countSeq (revS p) k = countSeq p (m - k) := by
  rw [countSeq_eq _ k (by omega), countSeq_eq _ (m - k) (by omega), localAlpha_revS]
  congr 1; apply Fin.ext; simp only [Fin.val_rev]; omega

theorem xor_cancel3 (x s t : Nat) (h : x = x ^^^ s ^^^ t) : s = t := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (Nat.testBit · i) h
  simp only [Nat.testBit_xor] at this
  revert this
  cases x.testBit i <;> cases s.testBit i <;> cases t.testBit i <;> decide

theorem pathDir_revS {m : Nat} (p : Snake m) (i : Nat) (hi : i < m) :
    pathDir (revS p) i = pathDir p (m - i - 1) := by
  have h1 := vertex_succ_eq (revS p) i hi
  have h2 := vertex_succ_eq p (m - i - 1) (by omega)
  have e1 : (revS p).vertex ⟨i + 1, by omega⟩ = p.vertex ⟨m - i - 1, by omega⟩ := by
    show p.vertex (Fin.rev _) = _; congr 1; apply Fin.ext; simp [Fin.val_rev]; omega
  have e2 : (revS p).vertex ⟨i, by omega⟩ = p.vertex ⟨m - i - 1 + 1, by omega⟩ := by
    show p.vertex (Fin.rev _) = _; congr 1; apply Fin.ext; simp [Fin.val_rev]; omega
  rw [e1, e2, h2] at h1
  have h3 := congrArg Fin.val h1
  simp only [Snake9.vxor, Snake9.unit] at h3
  have h4 := xor_cancel3 _ _ _ h3
  exact (Nat.pow_right_injective (le_refl 2) h4).symm

theorem dl_revS {m : Nat} (p : Snake m) (j L : Nat) (hj : j + L ≤ m) :
    dl (revS p) (m - (j + L)) L = (dl p j L).reverse := by
  apply List.ext_getElem
  · simp [dl]
  · intro i h1 h2
    simp only [dl, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
      List.length_range]
    simp [dl] at h1
    rw [pathDir_revS p _ (by omega)]
    congr 1; omega

theorem vtx_revS {m : Nat} (p : Snake m) (k : Nat) (hk : k ≤ m) : vtx (revS p) k = vtx p (m - k) := by
  rw [vtx_eq _ hk, vtx_eq _ (by omega)]
  show (p.vertex (Fin.rev _)).val = _
  congr 2; apply Fin.ext; simp only [Fin.val_rev]; omega

end S235
