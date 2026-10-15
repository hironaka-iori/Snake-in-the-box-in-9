import OneTwoDispatch
import Aggregate248

namespace Snake9
open SquareIncidence

theorem one_two_configuration_impossible {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : OneTwoRoot p a b c d) (f : TwoMissingAtNeighbor p a c) : False := by
  apply oneTwoRoot_impossible_of_nonb h f
  intro e x y hea heb hec hed hxa hxb hxc hya hyb hyc hxy hF
  exact h.be_nonb_false f e x y hea heb hec hed hxa hxb hxc hya hyb hyc hxy hF

theorem adjacent_internal_one_two_impossible {m : Nat} (p : Snake m)
    (i j : Fin (m+1)) (hi0 : 0 < i.val) (him : i.val < m)
    (hj0 : 0 < j.val) (hjm : j.val < m) (hadj : Adj (p.vertex i) (p.vertex j)) :
    ¬ (localAlpha p i = 1 ∧ localAlpha p j = 2) := by
  rintro ⟨hi,hj⟩
  obtain ⟨config⟩ := oneTwoConfig_of_adjacent_internal p i j hi0 him hj0 hjm hadj hi hj
  exact one_two_configuration_impossible config.root config.missing

theorem upper_bound_248 {m : Nat} (p : Snake m) : m ≤ 248 := by
  apply upper_248_of_no_adjacent_one_two p
  intro i j hi0 him hj0 hjm hadj
  exact adjacent_internal_one_two_impossible p i j hi0 him hj0 hjm hadj

theorem verified_interval_191_248 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 248 := by
  refine ⟨lower_bound,?_⟩
  rintro m ⟨p⟩
  exact upper_bound_248 p

#print axioms one_two_configuration_impossible
#print axioms adjacent_internal_one_two_impossible
#print axioms upper_bound_248
#print axioms verified_interval_191_248
end Snake9
