import Lift5
/-! # The facet-split reduction: a(9) bounds from one statement about induced linear forests of Q8

`snake_le_of_noPit`: if no induced linear forest of Q8 with at most 13 paths has `L` vertices (in the
form `NoPit 13 L 64`, the semantics of milestone 29's level-encoded CNF), then every snake in Q9 has at
most `2 L - 3` edges.  No other premise: the cap a(9) <= 231 is not used (a prefix of `2 L - 2` edges
is cut, so the least-used coordinate is crossed at most 25 times).

Proof: cut a prefix with `2 L - 2` edges; take a coordinate `i` crossed at most 25 times and the facet
`bit i = b` holding at least `L` of its `2 L - 1` vertices; keep its first `L` vertices.  Projected to
Q8 they form a set with degree <= 2 (neighbours inside the facet are consecutive on the snake), a level
function (distance to the nearer end of the run, <= 57), and endpoint sum `2 (#runs) <= 26`. -/
set_option linter.deprecated false
namespace Dim8Lift
open Snake9

theorem cnt_split (n : Nat) (p : Nat → Bool) : cnt n p + cnt n (fun t => !p t) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cnt_succ, cnt_succ]; cases p n <;> simp <;> omega

theorem exists_hit (y : Nat → Bool) (L : Nat) (hL : 1 ≤ L) :
    ∀ N, L ≤ cnt N y → ∃ j, j < N ∧ y j = true ∧ cnt (j + 1) y = L := by
  intro N
  induction N with
  | zero => intro h; simp at h; omega
  | succ N ih =>
    intro h
    by_cases h' : L ≤ cnt N y
    · obtain ⟨j, hj, hy, hc⟩ := ih h'; exact ⟨j, by omega, hy, hc⟩
    · rw [cnt_succ] at h
      by_cases hy : y N = true
      · rw [if_pos hy] at h; exact ⟨N, by omega, hy, by rw [cnt_succ, if_pos hy]; omega⟩
      · rw [if_neg hy] at h; omega

theorem pit_of_snake {L : Nat} (h2 : 2 ≤ L) (h116 : L ≤ 116) (q : Snake (2 * L - 2)) :
    ∃ S ℓ, Pit 13 L 64 S ℓ := by
  obtain ⟨i, hi, hk⟩ := exists_dir q (by omega)
  -- a facet with at least L of the 2L - 1 vertices
  have hsplit := cnt_split (2 * L - 2 + 1) (fun t => (V q t).testBit i)
  have hb : ∃ b : Bool, L ≤ cnt (2 * L - 2 + 1) (yy q i b) := by
    by_cases h : L ≤ cnt (2 * L - 2 + 1) (fun t => (V q t).testBit i)
    · refine ⟨true, ?_⟩
      have : cnt (2 * L - 2 + 1) (yy q i true) = cnt (2 * L - 2 + 1) (fun t => (V q t).testBit i) := by
        unfold cnt yy; apply sm_congr; intro t _; cases h : (V q t).testBit i <;> simp [h]
      omega
    · refine ⟨false, ?_⟩
      have : cnt (2 * L - 2 + 1) (yy q i false) = cnt (2 * L - 2 + 1) (fun t => !(V q t).testBit i) := by
        unfold cnt yy; apply sm_congr; intro t _; cases h : (V q t).testBit i <;> simp [h]
      omega
  obtain ⟨b, hbL⟩ := hb
  obtain ⟨j1, hj1, hyj, hcj⟩ := exists_hit (yy q i b) L (by omega) _ hbL
  have hj : j1 ≤ 2 * L - 2 := by omega
  refine ⟨SS q i b j1, ell q i b j1, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u hu a a' a'' h1 h2 h3 s0 s1 s2
    exact deg_ok hi hj hu h1 h2 h3 s0 s1 s2
  · intro u _
    unfold ell; split
    · have ⟨t, ht, hy, e⟩ := (SS_iff q i b j1 u).mp (by assumption)
      rw [← e, tOf_eq hi hj ht hy]
      have := lv_bound (q := q) (i := i) (b := b) ht hy; omega
    · exact Nat.le_refl _
  · intro u hu h
    exact lvl_ok hi hj (by omega) hu h
  · exact ends_ok hi hj hyj hk
  · rw [card_ok hi hj]; omega

/-- **Reduction.** No 13-path induced linear forest of Q8 on `L` vertices ⟹ every snake in Q9 has at
most `2 L - 3` edges. -/
theorem snake_le_of_noPit {L : Nat} (h2 : 2 ≤ L) (h116 : L ≤ 116) (hp : NoPit 13 L 64) :
    ∀ {m : Nat}, Snake m → m ≤ 2 * L - 3 := by
  intro m p
  apply Classical.byContradiction
  intro hm
  obtain ⟨S, ℓ, h⟩ := pit_of_snake h2 h116 (takePrefix p (k := 2 * L - 2) (by omega))
  exact hp S ℓ h

theorem upper_229_of_noPit (hp : NoPit 13 116 64) : ∀ {m : Nat}, Snake m → m ≤ 229 :=
  snake_le_of_noPit (by decide) (by decide) hp
theorem upper_227_of_noPit (hp : NoPit 13 115 64) : ∀ {m : Nat}, Snake m → m ≤ 227 :=
  snake_le_of_noPit (by decide) (by decide) hp
theorem upper_225_of_noPit (hp : NoPit 13 114 64) : ∀ {m : Nat}, Snake m → m ≤ 225 :=
  snake_le_of_noPit (by decide) (by decide) hp
theorem upper_223_of_noPit (hp : NoPit 13 113 64) : ∀ {m : Nat}, Snake m → m ≤ 223 :=
  snake_le_of_noPit (by decide) (by decide) hp

end Dim8Lift

#print axioms Dim8Lift.snake_le_of_noPit
#print axioms Dim8Lift.upper_229_of_noPit
#print axioms Dim8Lift.upper_223_of_noPit
