import NormalizeAdjacentSingletons
import AdjacentSingletonExclusion

namespace Snake9
open SquareIncidence

theorem adjacent_internal_alpha_one_impossible {m : Nat} (p : Snake m)
    (i j : Fin (m+1)) (hi0 : 0 < i.val) (him : i.val < m)
    (hj0 : 0 < j.val) (hjm : j.val < m) (hadj : Adj (p.vertex i) (p.vertex j)) :
    ¬ (localAlpha p i = 1 ∧ localAlpha p j = 1) := by
  rintro ⟨hi,hj⟩
  obtain ⟨h⟩ := config_of_adjacent_internal p i j hi0 him hj0 hjm hadj hi hj
  let q := translate p (p.vertex i)
  have hc : AdjacentConfig q h.a h.b h.c h.d h.e :=
    ⟨h.hab,h.hac,h.hbc,h.had,h.hbd,h.hcd,h.hae,h.hbe,h.hce,
     h.ha,h.hb,h.hacsel,h.cover,h.qcover,h.forced,h.qforced⟩
  exact adjacent_configuration_impossible q h.a h.b h.c h.d h.e hc

theorem upper_bound_251 {m : Nat} (p : Snake m) : m ≤ 251 := by
  apply upper_251_of_no_adjacent_internal_singletons p
  intro i hi hm
  exact adjacent_internal_alpha_one_impossible p i.castSucc i.succ hi
    (by change i.val < m; exact i.isLt)
    (by change 0 < i.val + 1; omega) hm ((path_adj_iff p _ _).mpr (Or.inl rfl))

theorem verified_interval_191_251 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 251 := by
  refine ⟨lower_bound,?_⟩
  rintro m ⟨p⟩
  exact upper_bound_251 p

#print axioms adjacent_internal_alpha_one_impossible
#print axioms upper_bound_251
#print axioms verified_interval_191_251
end Snake9
