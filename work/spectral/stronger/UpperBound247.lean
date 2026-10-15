import SmallPairFamilies
import EndpointGeometry
import Aggregate247

namespace Snake9
open SquareIncidence

theorem endpoint_missing_config_impossible {m : Nat} {p : Snake m} {a : Coord}
    (h : EndpointMissingConfig p a) : False := by
  rcases small_pair_family_cases h.F a h.Fcard h.edge_card h.avoids with
    ⟨j,hji,hj⟩ | ⟨u,v,hua,hva,huv,hu,hv,hpartner⟩
  · exact h.three_isolated_false (j 0) (j 1) (j 2) (hj 0).1 (hj 1).1 (hj 2).1
      (fun he => (by decide : (0 : Fin 3)≠1) (hji he))
      (fun he => (by decide : (0 : Fin 3)≠2) (hji he))
      (fun he => (by decide : (1 : Fin 3)≠2) (hji he))
      (hj 0).2 (hj 1).2 (hj 2).2
  · apply h.matching_false u v huv hua hva hu hv
    intro t hta htu htv
    obtain ⟨j,hja,hju,hjv,hjt,hj⟩ := hpartner t hta htu htv
    exact ⟨j,hja,hju,hjv,hjt,fun k _ _ hk => hj k hk⟩

theorem endpoint_alpha_ge_four {m : Nat} (p : Snake m) (i : Fin (m+1))
    (hm : 1≤m) (hi : i.val=0 ∨ i.val=m) : 4≤localAlpha p i := by
  by_contra hn
  have hsmall : localAlpha p i≤3 := by omega
  obtain ⟨a,⟨config⟩⟩ := endpointMissingConfig_of_small_alpha p i hm hi hsmall
  exact endpoint_missing_config_impossible config

theorem upper_bound_247 {m : Nat} (p : Snake m) : m≤247 := by
  by_cases hm : m=0
  · omega
  have hpos : 1≤m := by omega
  apply upper_247_of_endpoint_alpha p
  · exact endpoint_alpha_ge_four p 0 hpos (Or.inl rfl)
  · exact endpoint_alpha_ge_four p (Fin.last m) hpos (Or.inr rfl)

theorem verified_interval_191_247 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m≤247 := by
  refine ⟨lower_bound,?_⟩
  rintro m ⟨p⟩
  exact upper_bound_247 p

#print axioms endpoint_missing_config_impossible
#print axioms endpoint_alpha_ge_four
#print axioms upper_bound_247
#print axioms verified_interval_191_247
end Snake9
