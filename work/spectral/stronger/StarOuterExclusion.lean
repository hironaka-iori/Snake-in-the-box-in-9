import StarOuterEndpointCount

namespace Snake9
open Finset Classical
noncomputable section

theorem StarOuterConfig.impossible {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : StarOuterConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) : False := by
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.outer.hab,h.outer.hac,
      h.outer.had,h.outer.hbc,h.outer.hbd,h.outer.hcd]
  have hcR : c∉distinctR a b c d := by simp [distinctR]
  obtain ⟨hI,y,hy,hyf,hfy,hncy⟩ := star_outer_small_endpoint_count
    (distinctR a b c d) c h.e h.f f.F hR hcR hFcard f.edge_card (h.endpoint_resource_count f)
  obtain ⟨u,v,huv,hIuv⟩ := Finset.card_eq_two.mp hI
  have hu : u∈starIsolatedIndices (distinctR a b c d) f.F := by rw [hIuv]; simp
  have hv : v∈starIsolatedIndices (distinctR a b c d) f.F := by rw [hIuv]; simp
  obtain ⟨huR,huF⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨hvR,hvF⟩ := Finset.mem_sdiff.mp hv
  have hU : ∀s∈f.F,u∉s := fun s hs hus => huF (Finset.mem_biUnion.mpr ⟨s,hs,hus⟩)
  have hV : ∀s∈f.F,v∉s := fun s hs hvs => hvF (Finset.mem_biUnion.mpr ⟨s,hs,hvs⟩)
  exact h.residual_impossible f u v y huR hvR huv hU hV hy hyf hfy hncy

#print axioms StarOuterConfig.impossible
end
end Snake9
