import ShareWin
import Win235Norm
/-!
# Shares are invariant under cube automorphisms; normalising a window with its shares

* `shareTerm_translate`, `shareTerm_permSnake`: a share term is the same after translating the
  snake, and after permuting coordinates when the direction and the pair are permuted along.
* `share_cubeMap`: `share (cubeMap σ x p) i = share p i`, hence `shareSeq` and `windowShareK` agree.
* `norm_canon_share`: as `S235.norm_canon`, with the share sequence kept as well.
* `shareRef_window`: refuted share CNFs for every canonical shape of the list `sh` give the share
  lower bound for every window of a snake whose canonical shape is listed.
-/
namespace SH234
open Snake9 Snake9.SquareIncidence Snake9.WindowAutomaton Snake9.CubePerm Snake9.ShareBonus S235
open Classical

/-! ### Translations -/

theorem shareTerm_translate {m : Nat} (p : Snake m) (t v : Vertex) (k : Coord) (ab : AxisPair) :
    shareTerm (translate p t) k ab (vxor t v) = shareTerm p k ab v := by
  unfold shareTerm empty sqCount selected
  simp only [translate_flip, inPath_translate_iff]

theorem share_translate {m : Nat} (p : Snake m) (t : Vertex) (i : Fin (m+1)) :
    share (translate p t) i = share p i := by
  unfold share vertexShare
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro ab _
  exact shareTerm_translate p t (p.vertex i) k ab

/-! ### Coordinate permutations -/

theorem inPath_permSnake_flip {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (a : Coord) (w : Vertex) :
    InPath (permSnake σ p) (flip (σ a) (permV σ w)) ↔ InPath p (flip a w) := by
  rw [← permV_flip, inPath_permV_iff]

theorem empty_permSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (ab : AxisPair) (v : Vertex) :
    empty (permSnake σ p) (permPair σ ab) (permV σ v) = empty p ab v := by
  unfold permPair
  split
  · unfold empty
    dsimp only
    simp only [inPath_permSnake_flip, inPath_permV_iff, ← permV_flip]
  · unfold empty
    dsimp only
    simp only [inPath_permSnake_flip, inPath_permV_iff, ← permV_flip]
    rw [flip_commute ab.val.1 ab.val.2 v]
    exact if_congr (by tauto) rfl rfl

theorem sqCount_permSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (ab : AxisPair) (v : Vertex) :
    sqCount (permSnake σ p) (permPair σ ab) (permV σ v) = sqCount p ab v := by
  unfold permPair
  split
  · unfold sqCount selected
    dsimp only
    simp only [inPath_permSnake_flip, inPath_permV_iff, ← permV_flip]
  · unfold sqCount selected
    dsimp only
    simp only [inPath_permSnake_flip, inPath_permV_iff, ← permV_flip]
    rw [flip_commute ab.val.1 ab.val.2 v]
    omega

theorem offAxis_perm (σ : Equiv.Perm Coord) (k : Coord) (ab : AxisPair) :
    offAxis (σ k) (permPair σ ab) ↔ offAxis k ab := by
  unfold offAxis permPair
  split <;> simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq] <;> tauto

theorem shareTerm_permSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (k : Coord) (ab : AxisPair)
    (v : Vertex) : shareTerm (permSnake σ p) (σ k) (permPair σ ab) (permV σ v) = shareTerm p k ab v := by
  unfold shareTerm
  rw [← permV_flip, empty_permSnake, sqCount_permSnake]
  exact if_congr (offAxis_perm σ k ab) rfl rfl

theorem share_permSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (i : Fin (m+1)) :
    share (permSnake σ p) i = share p i := by
  unfold share vertexShare
  rw [permSnake_vertex, ← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl; intro k _
  rw [← Equiv.sum_comp (permPairEquiv σ)]
  apply Finset.sum_congr rfl; intro ab _
  exact shareTerm_permSnake σ p k ab (p.vertex i)

theorem share_cubeMap {m : Nat} (σ : Equiv.Perm Coord) (x : Vertex) (p : Snake m) (i : Fin (m+1)) :
    share (cubeMap σ x p) i = share p i := by
  unfold cubeMap
  rw [share_permSnake, share_translate]

theorem shareSeq_cubeMap {m : Nat} (σ : Equiv.Perm Coord) (x : Vertex) (p : Snake m) (c : Nat) :
    shareSeq (cubeMap σ x p) c = shareSeq p c := by
  unfold shareSeq; split
  · exact share_cubeMap σ x p _
  · rfl

/-! ### Normalisation keeping the shares -/

theorem norm_canon_share {m : Nat} (p : Snake m) (j L : Nat) (hj : j + L ≤ m) :
    ∃ q : Snake m, (∀ i ≤ L, vtx q (j + i) = wv (canon (dl p j L)) i) ∧
      ∀ k, shareSeq q k = shareSeq p k := by
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
  refine ⟨q, ?_, fun k => shareSeq_cubeMap σ _ p k⟩
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

theorem windowShareK_congr {m : Nat} {p q : Snake m} (h : ∀ k, shareSeq q k = shareSeq p k) (n j : Nat) :
    windowShareK q n j = windowShareK p n j := by
  unfold windowShareK
  exact Finset.sum_congr rfl (fun c _ => h _)

theorem dl_eq_blockList {m : Nat} (p : Snake m) (j L : Nat) : dl p j L = blockList p j L := by
  unfold dl blockList
  rw [List.range'_eq_map_range, List.map_map]
  rfl

/-- Per-shape share refutations give the share bound for every window whose canonical shape is
listed. -/
theorem shareRef_window {LB L : Nat} {sh : List (List Nat)} (hL : 1 ≤ L)
    (href : ∀ s ∈ sh, ShareRef s LB) {m : Nat} (p : Snake m) (j : Nat) (hj : j + L ≤ m)
    (hmem : canon (blockList p j L) ∈ sh) : LB ≤ windowShareK p (L - 1) j := by
  obtain ⟨q, hv, hs⟩ := norm_canon_share p j L hj
  rw [dl_eq_blockList] at hv
  have hlen : (canon (blockList p j L)).length = L := by rw [length_canon]; simp [blockList]
  have := href _ hmem q j (by rw [hlen]; exact hj) (by rw [hlen]; exact hv)
  rw [hlen, windowShareK_congr hs] at this
  exact this

end SH234
