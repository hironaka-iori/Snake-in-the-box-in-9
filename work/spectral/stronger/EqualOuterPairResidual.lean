import EqualOuterPairForce
import EqualOuterPairStar

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

namespace EqualOuterPairConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : EqualOuterPairConfig p a b c d)
include h

theorem common_missing_impossible (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (hm : ({h.i,h.j}:Finset Coord)∈f.F) : False := by
  have hclean := h.no_clean_missing_pair f hFcard
  have hdis := h.clean_pair_disjoint h.i h.j h.clean_avoids.1 h.clean_avoids.2.1
  obtain ⟨E,hEne,hEF,hFE⟩ := pair_family_other_edge f.F {h.i,h.j} hFcard hm
  obtain ⟨u,huinj,hu⟩ := outside_edge_two_isolated h.clean f.F h.clean_card hFcard f.edge_card
    hclean {h.i,h.j} hm hdis
  have huv : u 0≠u 1 := fun he => (by decide : (0:Fin 2)≠1) (huinj he)
  have close (k t : Coord) (hk : k∈h.clean) (ht : t∉h.clean) (hEt : E={t,k}) : False := by
    have htE : t∈E := by rw [hEt]; simp
    have htA := f.avoids E hEF t htE
    have hF : f.F={{h.i,h.j},{t,k}} := by rw [hFE,hEt]
    by_cases htc : t=c
    · subst t
      exact h.star_c_middle_impossible f k (u 0) (u 1) hk (hu 0).1 (hu 1).1 huv (hu 0).2 (hu 1).2 hF
    by_cases htd : t=d
    · subst t
      exact h.star_d_middle_impossible f k (u 0) (u 1) hk (hu 0).1 (hu 1).1 huv (hu 0).2 (hu 1).2 hF
    by_cases hti : t=h.i
    · rw [hti] at hF
      exact h.incident_middle_impossible f k (u 0) (u 1) hk (hu 0).1 (hu 1).1 huv (hu 0).2 (hu 1).2 hF
    by_cases htj : t=h.j
    · rw [htj] at hF
      exact h.incident_j_middle_impossible f k (u 0) (u 1) hk (hu 0).1 (hu 1).1 huv (hu 0).2 (hu 1).2 hF
    exact ht ((h.mem_clean t).mpr ⟨(mem_distinctR _ _ _ _ _).mpr ⟨htA.1,htA.2,htc,htd⟩,hti,htj⟩)
  obtain ⟨x,y,hxy,hExy⟩ := Finset.card_eq_two.mp (f.edge_card E hEF)
  by_cases hx : x∈h.clean
  · have hy : y∉h.clean := by
      intro hy
      apply hclean E hEF
      rw [hExy]
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact Finset.mem_singleton.mp hz ▸ hy
    exact close x y hx hy (by rw [hExy]; exact Finset.pair_comm x y)
  by_cases hy : y∈h.clean
  · exact close y x hy hx hExy
  have hEd : Disjoint E h.clean := by
    rw [hExy]
    exact h.clean_pair_disjoint x y hx hy
  obtain ⟨v,hvinj,hv⟩ := two_outside_edges_three_isolated h.clean f.F {h.i,h.j} E h.clean_card hFE hdis hEd
  exact h.three_clean_isolated_false f v hvinj hv

end EqualOuterPairConfig
#print axioms EqualOuterPairConfig.common_missing_impossible
end
end Snake9
