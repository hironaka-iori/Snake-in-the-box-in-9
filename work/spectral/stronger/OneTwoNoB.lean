import FiniteEndpointCounting
import OneTwoGeometry

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

namespace OneTwoRoot
variable {m : Nat} {p : Snake m} {a b c d : Coord}
  (h : OneTwoRoot p a b c d) (f : TwoMissingAtNeighbor p a c)
include h f

theorem no_b_impossible (hnob : ∀ s ∈ f.F, b ∉ s) : False := by
  obtain ⟨coords,hcoords,hinj⟩ := exists_five_coords_outside_four a b c d
  let W : Finset Coord := Finset.univ.image coords
  have hW : W.card = 5 := by simp [W,Finset.card_image_of_injective _ hinj]
  have avoids (k : Coord) (hk : k ∈ W) : k≠a ∧ k≠b ∧ k≠c ∧ k≠d := by
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hk
    exact hcoords r
  let I := W.filter (fun k => AtMostOneNeighbor p (triple a b k))
  let J := f.F.filter (fun s => AtMostOneNeighbor p (edgeVertex s))
  have hIs (k : Coord) (hk : k∈I) :
      InPath p (triple a b k) ∧ AtMostOneNeighbor p (triple a b k) := by
    obtain ⟨hk,hl⟩ := Finset.mem_filter.mp hk
    have ha := avoids k hk
    refine ⟨h.selected_t f k ha.1 ha.2.1 ha.2.2.1 ?_,hl⟩
    exact fun hs => hnob _ hs (by simp)
  have hJs (s : Finset Coord) (hs : s∈J) :
      InPath p (edgeVertex s) ∧ AtMostOneNeighbor p (edgeVertex s) := by
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    obtain ⟨i,j,hij,he,hv⟩ := edgeVertex_eq_pair s (f.edge_card s hs)
    have hi : i∈s := by rw [he]; simp
    have hj : j∈s := by rw [he]; simp
    have hia := (f.avoids s hs i hi).1
    have hic := (f.avoids s hs i hi).2
    have hja := (f.avoids s hs j hj).1
    have hjc := (f.avoids s hs j hj).2
    have hib : i≠b := fun he => hnob s hs (he ▸ hi)
    have hjb : j≠b := fun he => hnob s hs (he ▸ hj)
    have hpair : InPath p (pair i j) :=
      h.selected_pair i j hij hia hib hja hjb (by tauto)
    exact ⟨hv.symm ▸ hpair,hl⟩
  have hfi : Set.InjOn (fun k => triple a b k) I := by
    intro i hi j hj he
    exact triple_injective_right a b i j he
  have hgi : Set.InjOn edgeVertex J := by
    intro s hs t ht he
    exact edgeVertex_injective_on_pairs s t (f.edge_card s (Finset.mem_filter.mp hs).1)
      (f.edge_card t (Finset.mem_filter.mp ht).1) he
  have hdis : ∀ k∈I, ∀ s∈J, triple a b k ≠ edgeVertex s := by
    intro k hk s hs he
    have hka := (avoids k (Finset.mem_filter.mp hk).1).1
    have hsF := (Finset.mem_filter.mp hs).1
    obtain ⟨i,j,hij,hpair,hv⟩ := edgeVertex_eq_pair s (f.edge_card s hsF)
    have hi : i∈s := by rw [hpair]; simp
    have hj : j∈s := by rw [hpair]; simp
    have hia := (f.avoids s hsF i hi).1
    have hja := (f.avoids s hsF j hj).1
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) (he.trans hv)
    simp [bit_triple,bit_pair,Ne.symm h.hab,hka,hia,hja] at hb
  have hcost : I.card + J.card ≤ 2 :=
    two_endpoint_images_card p I J (fun k => triple a b k) edgeVertex hfi hgi hIs hJs hdis
  apply five_not_covered_by_two_endpoints W I J hW hcost
  · intro s hs
    exact f.edge_card s (Finset.mem_filter.mp hs).1
  · intro k hk
    have ha := avoids k hk
    rcases h.no_b_endpoint_alternative f hnob k ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 with hl | ⟨j,_,_,_,hjk,hs,hl⟩
    · exact Or.inl (Finset.mem_filter.mpr ⟨hk,hl⟩)
    · right
      refine ⟨{k,j},Finset.mem_filter.mpr ⟨hs,?_⟩,by simp⟩
      simpa only [edgeVertex_pair k j (Ne.symm hjk)] using hl

end OneTwoRoot
#print axioms OneTwoRoot.no_b_impossible
end
end Snake9
