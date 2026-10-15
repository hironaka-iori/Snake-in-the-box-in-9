import NormalizeOneTwo

namespace Snake9
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem exists_neighbor_ne {m : Nat} (p : Snake m) (v u : Vertex)
    (hn : ¬ AtMostOneNeighbor p v) :
    ∃ w, InPath p w ∧ Adj v w ∧ w≠u := by
  by_contra hh
  push_neg at hh
  apply hn
  intro x y hx hy hax hay
  exact (hh x hx hax).trans (hh y hy hay).symm

namespace OneTwoRoot
variable {m : Nat} {p : Snake m} {a b c d : Coord}
  (h : OneTwoRoot p a b c d) (f : TwoMissingAtNeighbor p a c)
include h f

theorem selected_t (k : Coord) (hka : k≠a) (hkb : k≠b) (hkc : k≠c)
    (hbk : ({b,k} : Finset Coord) ∉ f.F) : InPath p (triple a b k) :=
  (f.selected_iff b k (Ne.symm hkb) (Ne.symm h.hab) h.hbc hka hkc).mpr hbk

theorem connection_missing_or_hole (k j : Coord)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c)
    (hja : j≠a) (hjb : j≠b) (hjc : j≠c) (hjk : j≠k)
    (ht : InPath p (triple a b k)) (hq : InPath p (quad a b k j)) :
    ({b,j} : Finset Coord) ∈ f.F ∨ ({k,j} : Finset Coord) ∈ f.F := by
  by_contra hn
  push_neg at hn
  have htj := h.selected_t f j hja hjb hjc hn.1
  have hakj := (f.selected_iff k j (Ne.symm hjk) hka hkc hja hjc).mpr hn.2
  exact ordinary_quad_absent p a b k j h.hab hkb hjb (Ne.symm hjk) ht htj hakj hq

theorem no_b_endpoint_alternative (hnob : ∀ s∈f.F, b∉s)
    (k : Coord) (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d) :
    AtMostOneNeighbor p (triple a b k) ∨ ∃ j : Coord,
      j≠a ∧ j≠b ∧ j≠c ∧ j≠k ∧ ({k,j} : Finset Coord)∈f.F ∧
      AtMostOneNeighbor p (pair k j) := by
  have hbk : ({b,k} : Finset Coord)∉f.F := fun hm => hnob _ hm (by simp)
  have ht := h.selected_t f k hka hkb hkc hbk
  by_cases hn : AtMostOneNeighbor p (triple a b k)
  · exact Or.inl hn
  right
  obtain ⟨w,hw,hadj,hne⟩ := exists_neighbor_ne p (triple a b k) (quad a b c k) hn
  rcases h.triple_neighbor_cover_general k hka hkb hkc hkd w hw hadj with he | ⟨j,hja,hjb,hjc,hjk,he⟩
  · exact False.elim (hne he)
  have hq : InPath p (quad a b k j) := he ▸ hw
  have hbj : ({b,j} : Finset Coord)∉f.F := fun hm => hnob _ hm (by simp)
  have hkj := (h.connection_missing_or_hole f k j hka hkb hkc hja hjb hjc hjk ht hq).resolve_left hbj
  have htj := h.selected_t f j hja hjb hjc hbj
  have hmiss : ¬ InPath p (triple a k j) := by
    intro hs
    exact (f.selected_iff k j (Ne.symm hjk) hka hkc hja hjc).mp hs hkj
  exact ⟨j,hja,hjb,hjc,hjk,hkj,
    h.missing_connection_low_degree k j hka hkb hkc hkd hja hjb hjc (Ne.symm hjk) hq ht htj hmiss⟩

end OneTwoRoot
#print axioms OneTwoRoot.no_b_endpoint_alternative
end Snake9
