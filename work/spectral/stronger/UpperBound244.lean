import W223G1Inst
import W223G1CheckRep
import W223G1CheckDis
import W223RepMain
import W223DisMain
import CubePermutation
import Aggregate244Conditional
import UpperBound245
/-!
# No snake in `Q_9` has a (2,2,3) window; hence every snake has length at most 244

(a) Window shapes: three consecutive internal vertices with local singleton counts `2,2,3`
have path directions `d0,d1,d2,d3` (edges `r..r+3`) with `d0,d1,d2` distinct and `d3 ∉ {d1,d2}`.
After the cube automorphism of `CubePerm.exists_normalizing_cubeMap` the window is
`0,1,3,7,6` (`d3 = d0`) or `0,1,3,7,15` (`d3` new).
(b) For these the snake's vertex set satisfies `Hyp tabRep` / `Hyp tabDis` (`W223G1Inst`), all
used clauses pass the checker (`W223G1CheckRep/Dis`), the checker is sound (`W223G1Sound`),
and the used-clause CNFs are unsatisfiable (G2: `w223_rep_unsat`, `w223_dis_unsat`).
(c) `upper_244_of_no_two_two_three` then gives `m ≤ 244`.
-/
namespace W223G1
open Snake9 Snake9.SquareIncidence WinCNF

theorem no_rep_window {m : Nat} (q : Snake m) (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = 6)
    (a1 : localAlpha q ⟨r+1, by omega⟩ = 2) (a2 : localAlpha q ⟨r+2, by omega⟩ = 2)
    (a3 : localAlpha q ⟨r+3, by omega⟩ = 3) : False :=
  no_hyp w223_rep_unsat blocksOK_rep check_rep (hyp_rep q r hr h0 h1 h2 h3 h4 a1 a2 a3)

theorem no_dis_window {m : Nat} (q : Snake m) (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = 15)
    (a1 : localAlpha q ⟨r+1, by omega⟩ = 2) (a2 : localAlpha q ⟨r+2, by omega⟩ = 2)
    (a3 : localAlpha q ⟨r+3, by omega⟩ = 3) : False :=
  no_hyp w223_dis_unsat blocksOK_dis check_dis (hyp_dis q r hr h0 h1 h2 h3 h4 a1 a2 a3)

/-! ### Directions along a snake -/

/-- The direction of edge `j` as a coordinate. -/
def dirC {m : Nat} (p : Snake m) (j : Nat) : Coord :=
  ⟨WindowAutomaton.pathDir p j, WindowAutomaton.pathDir_lt p j⟩

theorem vertex_succ_dir {m : Nat} (p : Snake m) (j : Nat) (hj : j < m) (a : Coord)
    (ha : WindowAutomaton.pathDir p j = a.val) :
    p.vertex ⟨j+1, by omega⟩ = vxor (p.vertex ⟨j, by omega⟩) (unit a) := by
  rw [CubePerm.vertex_succ_eq p j hj]
  congr 2
  exact Fin.ext ha

/-- Consecutive edge directions differ. -/
theorem dir_ne_succ {m : Nat} (p : Snake m) (j : Nat) (hj : j + 2 ≤ m) :
    dirC p j ≠ dirC p (j+1) := by
  intro he
  have e1 := vertex_succ_dir p j (by omega) (dirC p j) rfl
  have e2 := vertex_succ_dir p (j+1) (by omega) (dirC p j) (by rw [he]; rfl)
  rw [e1, vxor_cancel_right] at e2
  have := congrArg Fin.val (p.distinct _ _ e2)
  simp only at this
  omega

/-- Edge directions at distance two differ (otherwise the path has a chord). -/
theorem dir_ne_succ_succ {m : Nat} (p : Snake m) (j : Nat) (hj : j + 3 ≤ m) :
    dirC p j ≠ dirC p (j+2) := by
  intro he
  have e1 := vertex_succ_dir p j (by omega) (dirC p j) rfl
  have e2 := vertex_succ_dir p (j+1) (by omega) (dirC p (j+1)) rfl
  have e3 := vertex_succ_dir p (j+2) (by omega) (dirC p j) (by rw [he]; rfl)
  have hv : p.vertex ⟨j+3, by omega⟩ =
      SquareIncidence.flip (dirC p (j+1)) (p.vertex ⟨j, by omega⟩) := by
    rw [e3, e2, e1]
    unfold SquareIncidence.flip
    apply Fin.ext
    change ((_ ^^^ _) ^^^ _) ^^^ _ = _ ^^^ _
    rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm (unit (dirC p (j+1))).val,
      ← Nat.xor_assoc (unit (dirC p j)).val, Nat.xor_self, Nat.zero_xor]
  have hadj : Adj (p.vertex ⟨j, by omega⟩) (p.vertex ⟨j+3, by omega⟩) := by
    rw [hv]; exact flip_adj _ _
  have := (p.induced ⟨j, by omega⟩ ⟨j+3, by omega⟩ (by simp)).mp hadj
  simp at this

/-! ### (a)+(b): no (2,2,3) window -/

theorem no_223 {m : Nat} (p : Snake m) (r : Nat) (hr : r + 4 ≤ m)
    (h : localAlpha p ⟨r+1, by omega⟩ = 2 ∧ localAlpha p ⟨r+2, by omega⟩ = 2 ∧
      localAlpha p ⟨r+3, by omega⟩ = 3) : False := by
  obtain ⟨a1, a2, a3⟩ := h
  have n01 := dir_ne_succ p r (by omega)
  have n12 := dir_ne_succ p (r+1) (by omega)
  have n23 := dir_ne_succ p (r+2) (by omega)
  have n02 := dir_ne_succ_succ p r (by omega)
  have n13 := dir_ne_succ_succ p (r+1) (by omega)
  -- vertices of the normalised snake from its directions
  have walk : ∀ {σ : Equiv.Perm Coord} {x : Vertex} (d3 : Coord),
      (CubePerm.cubeMap σ x p).vertex ⟨r, by omega⟩ = 0 →
      WindowAutomaton.pathDir (CubePerm.cubeMap σ x p) r = 0 →
      WindowAutomaton.pathDir (CubePerm.cubeMap σ x p) (r+1) = 1 →
      WindowAutomaton.pathDir (CubePerm.cubeMap σ x p) (r+2) = 2 →
      WindowAutomaton.pathDir (CubePerm.cubeMap σ x p) (r+3) = d3.val →
      (CubePerm.cubeMap σ x p).vertex ⟨r+1, by omega⟩ = 1 ∧
      (CubePerm.cubeMap σ x p).vertex ⟨r+2, by omega⟩ = 3 ∧
      (CubePerm.cubeMap σ x p).vertex ⟨r+3, by omega⟩ = 7 ∧
      (CubePerm.cubeMap σ x p).vertex ⟨r+4, by omega⟩ = vxor 7 (unit d3) := by
    intro σ x d3 hv0 hd0 hd1 hd2 hd3
    have v1 := vertex_succ_dir (CubePerm.cubeMap σ x p) r (by omega) 0 hd0
    have v2 := vertex_succ_dir (CubePerm.cubeMap σ x p) (r+1) (by omega) 1 hd1
    have v3 := vertex_succ_dir (CubePerm.cubeMap σ x p) (r+2) (by omega) 2 hd2
    have v4 := vertex_succ_dir (CubePerm.cubeMap σ x p) (r+3) (by omega) d3 hd3
    rw [hv0] at v1
    rw [v1] at v2
    rw [v2] at v3
    rw [v3] at v4
    refine ⟨by rw [v1]; decide, by rw [v2]; decide, by rw [v3]; decide, by rw [v4]; congr 1⟩
  by_cases hrep : dirC p (r+3) = dirC p r
  · -- repeated direction: window 0,1,3,7,6
    obtain ⟨σ, x, hv0, hdir, halpha⟩ := CubePerm.exists_normalizing_cubeMap p ⟨r, by omega⟩
      [r, r+1, r+2] (by
        simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, not_or, or_false]
        exact ⟨⟨n01, n02⟩, n12, by simp, List.nodup_nil⟩)
      (by intro j hj; simp at hj; omega)
    have hd0 := hdir 0 (by simp)
    have hd1 := hdir 1 (by simp)
    have hd2 := hdir 2 (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hd0 hd1 hd2
    have hd3 : WindowAutomaton.pathDir (CubePerm.cubeMap σ x p) (r+3) = (0 : Coord).val := by
      rw [CubePerm.pathDir_cubeMap σ x p (r+3) (by omega)]
      have : (⟨WindowAutomaton.pathDir p (r+3), WindowAutomaton.pathDir_lt p (r+3)⟩ : Coord) =
          ⟨WindowAutomaton.pathDir p r, WindowAutomaton.pathDir_lt p r⟩ := hrep
      rw [this, ← CubePerm.pathDir_cubeMap σ x p r (by omega), hd0]
      rfl
    obtain ⟨v1, v2, v3, v4⟩ := walk 0 hv0 hd0 hd1 hd2 hd3
    exact no_rep_window _ r hr hv0 v1 v2 v3 (by rw [v4]; decide)
      (by rw [halpha]; exact a1) (by rw [halpha]; exact a2) (by rw [halpha]; exact a3)
  · -- new direction: window 0,1,3,7,15
    obtain ⟨σ, x, hv0, hdir, halpha⟩ := CubePerm.exists_normalizing_cubeMap p ⟨r, by omega⟩
      [r, r+1, r+2, r+3] (by
        simp only [List.map_cons, List.map_nil]
        refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr
          ⟨?_, List.nodup_singleton _⟩⟩⟩
        · simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or, or_false]
          exact ⟨n01, n02, Ne.symm hrep⟩
        · simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, not_or, or_false]
          exact ⟨n12, n13⟩
        · simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]
          exact n23)
      (by intro j hj; simp at hj; omega)
    have hd0 := hdir 0 (by simp)
    have hd1 := hdir 1 (by simp)
    have hd2 := hdir 2 (by simp)
    have hd3 := hdir 3 (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hd0 hd1 hd2 hd3
    obtain ⟨v1, v2, v3, v4⟩ := walk 3 hv0 hd0 hd1 hd2 hd3
    exact no_dis_window _ r hr hv0 v1 v2 v3 (by rw [v4]; decide)
      (by rw [halpha]; exact a1) (by rw [halpha]; exact a2) (by rw [halpha]; exact a3)

end W223G1

namespace Snake9

/-- **Unconditional bound**: every snake in the 9-cube has at most 244 edges. -/
theorem upper_bound_244 {m : Nat} (p : Snake m) : m ≤ 244 :=
  upper_244_of_no_two_two_three p (fun r hr h => W223G1.no_223 p r hr h)

theorem upper_bound_244' : ∀ m, Nonempty (Snake m) → m ≤ 244 :=
  fun _ ⟨p⟩ => upper_bound_244 p

/-- The verified interval: a 191-edge snake exists, and no snake has more than 244 edges. -/
theorem verified_interval_191_244 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 244 :=
  ⟨lower_bound, upper_bound_244'⟩

end Snake9

#print axioms W223G1.no_223
#print axioms Snake9.upper_bound_244
#print axioms Snake9.verified_interval_191_244
