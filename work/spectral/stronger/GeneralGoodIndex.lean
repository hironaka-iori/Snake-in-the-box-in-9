import GeneralMissingGeometry
import GeneralOneTwoLocal

namespace Snake9
open Finset Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

namespace OneTwoRoot
variable {m : Nat} {p : Snake m} {a b c d : Coord}
  (h : OneTwoRoot p a b c d) (f : MissingAtNeighbor p a c)
include h f

/-- A good ordinary coordinate has no missing edge to a missing b-row.
Every such coordinate demands an endpoint in its own listed group. -/
theorem good_index_endpoint_alternative (i : Coord)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    (hbi : ({b,i} : Finset Coord) ∉ f.F)
    (hgood : ∀ j, ({i,j} : Finset Coord) ∈ f.F → ({b,j} : Finset Coord) ∉ f.F) :
    AtMostOneNeighbor p (triple a b i) ∨
    (∃ j : Coord, j≠a ∧ j≠b ∧ j≠c ∧ j≠d ∧ j≠i ∧
      ({b,j} : Finset Coord) ∈ f.F ∧ AtMostOneNeighbor p (pair j i)) ∨
    (({b,d} : Finset Coord) ∈ f.F ∧
      (AtMostOneNeighbor p (pair c i) ∨ AtMostOneNeighbor p (pair d i))) ∨
    (({b,d} : Finset Coord) ∉ f.F ∧ ({d,i} : Finset Coord) ∈ f.F ∧
      AtMostOneNeighbor p (pair d i)) := by
  classical
  have ht := h.family_selected_t f i hia hib hic hbi
  by_cases hnt : AtMostOneNeighbor p (triple a b i)
  · exact Or.inl hnt
  right
  by_cases hh : ∃ j : Coord, j≠a ∧ j≠b ∧ j≠c ∧ j≠d ∧ j≠i ∧
      ({b,j} : Finset Coord) ∈ f.F ∧ AtMostOneNeighbor p (pair j i)
  · exact Or.inl hh
  right
  have hcvr : ∀ w, InPath p w → Adj (triple a b i) w →
      w=quad a b c i ∨ w=quad a b d i := by
    intro w hw hadj
    rcases h.triple_neighbor_cover_general i hia hib hic hid w hw hadj with
      he | ⟨j,hja,hjb,hjc,hji,he⟩
    · exact Or.inl he
    by_cases hjd : j=d
    · right
      simpa only [hjd,quad_swap_last a b i d] using he
    have hq : InPath p (quad a b i j) := he ▸ hw
    have hx := h.family_connection_missing_or_hole f i j hia hib hic hja hjb hjc hji ht hq
    by_cases hbj : ({b,j} : Finset Coord) ∈ f.F
    · have hij : ({i,j} : Finset Coord) ∉ f.F := fun hx => hgood j hx hbj
      have haji : InPath p (triple a j i) := by
        apply (f.selected_iff j i hji hja hjc hia hic).mpr
        simpa only [Finset.pair_comm j i] using hij
      have hlow := h.hole_connection_low_degree j i hja hjb hjc hjd hia hib hic hid hji
        (by simpa only [quad_swap_last a b i j] using hq) ht haji
      exact False.elim (hh ⟨j,hja,hjb,hjc,hjd,hji,hbj,hlow⟩)
    · have hij := hx.resolve_left hbj
      have htj := h.family_selected_t f j hja hjb hjc hbj
      have haij : ¬ InPath p (triple a i j) := by
        intro hs
        exact (f.selected_iff i j (Ne.symm hji) hia hic hja hjc).mp hs hij
      exact False.elim (h.missing_ordinary_connection_false i j hia hib hic hid
        hja hjb hjc hjd (Ne.symm hji) hq ht htj haij)
  by_cases hbd : ({b,d} : Finset Coord) ∈ f.F
  · left
    have hdi : ({d,i} : Finset Coord) ∉ f.F := by
      intro hm
      apply hgood d _ hbd
      simpa only [Finset.pair_comm d i] using hm
    have hadi := (f.selected_iff d i (Ne.symm hid) (Ne.symm h.had)
      (Ne.symm h.hcd) hia hic).mpr hdi
    exact ⟨hbd,(h.cycle_group_low_degree i hia hib hic hid ht hadi hcvr).resolve_left hnt⟩
  · right
    obtain ⟨w,hw,hadj,hne⟩ := exists_neighbor_ne p (triple a b i) (quad a b c i) hnt
    have he : w=quad a b d i := (hcvr w hw hadj).resolve_left hne
    have hq : InPath p (quad a b i d) := by
      simpa only [quad_swap_last a b d i] using (show InPath p (quad a b d i) from he ▸ hw)
    have hidF := (h.family_connection_missing_or_hole f i d hia hib hic
      (Ne.symm h.had) (Ne.symm h.hbd) (Ne.symm h.hcd) (Ne.symm hid) ht hq).resolve_left hbd
    have htd := h.family_selected_t f d (Ne.symm h.had) (Ne.symm h.hbd) (Ne.symm h.hcd) hbd
    have haid : ¬ InPath p (triple a i d) := by
      intro hs
      exact (f.selected_iff i d hid hia hic (Ne.symm h.had) (Ne.symm h.hcd)).mp hs hidF
    have hlow := h.missing_connection_low_degree i d hia hib hic hid (Ne.symm h.had)
      (Ne.symm h.hbd) (Ne.symm h.hcd) hid hq ht htd haid
    exact ⟨hbd,by simpa only [Finset.pair_comm i d] using hidF,
      by simpa only [pair_comm i d] using hlow⟩

end OneTwoRoot
#print axioms OneTwoRoot.good_index_endpoint_alternative
end Snake9
