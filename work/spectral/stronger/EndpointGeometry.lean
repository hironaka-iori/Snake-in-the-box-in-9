import OneTwoLocal
import EndpointMissingConfig

namespace Snake9
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem endpoint_pair_neighbor_cover {m : Nat} (p : Snake m)
    (a i j t : Coord) (hij : i≠j) (hia : i≠a) (hja : j≠a)
    (cover : ∀k, InPath p (unit k) → k=a)
    (hp : InPath p (pair i j))
    (hforced : ∀k, k≠a → k≠i → k≠j → k≠t →
      InPath p (pair i k) ∧ InPath p (pair j k)) :
    ∀w, InPath p w → Adj (pair i j) w →
      w=triple a i j ∨ w=triple i j t := by
  intro w hw hadj
  obtain ⟨k,rfl⟩ := neighbor_pair i j hadj
  by_cases hki : k=i
  · subst k
    rw [triple_cancel_left] at hw
    exact False.elim (hja (cover j hw))
  by_cases hkj : k=j
  · subst k
    rw [triple_cancel_right] at hw
    exact False.elim (hia (cover i hw))
  by_cases hka : k=a
  · subst k
    exact Or.inl (triple_rotate i j a)
  by_cases hkt : k=t
  · subst k
    exact Or.inr rfl
  have hf := hforced k hka hki hkj hkt
  exact False.elim (selected_triple_forbidden p i j k hij (Ne.symm hki)
    (Ne.symm hkj) hp hf.1 hf.2 hw)

theorem selected_pair_forbidden_two_triples {m : Nat} (p : Snake m)
    (a t u v : Coord) (hat : a≠t) (hau : a≠u) (hav : a≠v)
    (htu : t≠u) (htv : t≠v) (huv : u≠v)
    (ha : InPath p (unit a))
    (htuS : InPath p (triple a t u)) (htvS : InPath p (triple a t v)) :
    ¬ InPath p (pair a t) := by
  intro hp
  rcases selected_three_neighbors_repeat p hp ha htuS htvS
    (adj_symmetric (unit_pair_adj a t)) (pair_triple_adj a t u) (pair_triple_adj a t v)
    with he | he | he
  · have hb := congrArg (fun z : Vertex => z.val.testBit t.val) he
    simp [bit_unit,bit_triple,hat,Ne.symm htu] at hb
  · have hb := congrArg (fun z : Vertex => z.val.testBit t.val) he
    simp [bit_unit,bit_triple,hat,Ne.symm htv] at hb
  · exact huv (triple_injective_right a t u v he)

namespace EndpointMissingConfig
variable {m : Nat} {p : Snake m} {a : Coord} (h : EndpointMissingConfig p a)
include h

theorem isolated_pair_selected (u v : Coord) (huv : u≠v) (hua : u≠a) (hva : v≠a)
    (hu : ∀s∈h.F,u∉s) : InPath p (pair u v) := by
  apply (h.selected_iff u v huv hua hva).mpr
  intro hm
  exact hu _ hm (by simp)

theorem isolated_pair_low (u v : Coord) (huv : u≠v) (hua : u≠a) (hva : v≠a)
    (hu : ∀s∈h.F,u∉s) (hv : ∀s∈h.F,v∉s) : AtMostOneNeighbor p (pair u v) := by
  have hp := h.isolated_pair_selected u v huv hua hva hu
  have hcvr := endpoint_pair_neighbor_cover p a u v a huv hua hva h.cover hp
    (fun k hka hku hkv _ => ⟨h.isolated_pair_selected u k (Ne.symm hku) hua hka hu,
      h.isolated_pair_selected v k (Ne.symm hkv) hva hka hv⟩)
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair u v) w) : w=triple a u v := by
    rcases hcvr w hw hadj with he | he
    · exact he
    · exact he.trans (triple_rotate u v a)
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

theorem three_isolated_false (u v w : Coord)
    (hua : u≠a) (hva : v≠a) (hwa : w≠a)
    (huv : u≠v) (huw : u≠w) (hvw : v≠w)
    (hu : ∀s∈h.F,u∉s) (hv : ∀s∈h.F,v∉s) (hw : ∀s∈h.F,w∉s) : False := by
  have hpv := h.isolated_pair_selected u v huv hua hva hu
  have hpw := h.isolated_pair_selected u w huw hua hwa hu
  have hlv := h.isolated_pair_low u v huv hua hva hu hv
  have hlw := h.isolated_pair_low u w huw hua hwa hu hw
  rcases three_low_degree_vertices_repeat p h.hzero hpv hpw h.zero_low hlv hlw with he | he | he
  · exact pair_nonzero u v huv he.symm
  · exact pair_nonzero u w huw he.symm
  · exact hvw (pair_injective_right u v w he)

theorem other_not_low (u v : Coord) (huv : u≠v) (hua : u≠a) (hva : v≠a)
    (hu : ∀s∈h.F,u∉s) (hv : ∀s∈h.F,v∉s)
    (w : Vertex) (hw : InPath p w) (hw0 : w≠0) (hwuv : w≠pair u v) :
    ¬ AtMostOneNeighbor p w := by
  intro hl
  have hp := h.isolated_pair_selected u v huv hua hva hu
  have hlp := h.isolated_pair_low u v huv hua hva hu hv
  rcases three_low_degree_vertices_repeat p h.hzero hp hw h.zero_low hlp hl with he | he | he
  · exact pair_nonzero u v huv he.symm
  · exact hw0 he.symm
  · exact hwuv he.symm

theorem matching_false (u v : Coord) (huv : u≠v) (hua : u≠a) (hva : v≠a)
    (hu : ∀s∈h.F,u∉s) (hv : ∀s∈h.F,v∉s)
    (hpartner : ∀t, t≠a → t≠u → t≠v → ∃j,
      j≠a ∧ j≠u ∧ j≠v ∧ j≠t ∧
      ∀k, k≠a → k≠t → ({t,k} : Finset Coord)∈h.F → k=j) : False := by
  have triples (t : Coord) (hta : t≠a) (htu : t≠u) (htv : t≠v) :
      InPath p (triple a t u) ∧ InPath p (triple a t v) := by
    obtain ⟨j,hja,hju,hjv,hjt,hj⟩ := hpartner t hta htu htv
    have htp (k : Coord) (hka : k≠a) (hkt : k≠t) (hkj : k≠j) : InPath p (pair t k) := by
      apply (h.selected_iff t k (Ne.symm hkt) hta hka).mpr
      exact fun hm => hkj (hj k hka hkt hm)
    have one (z : Coord) (hza : z≠a) (htz : t≠z) (hz : ∀s∈h.F,z∉s) :
        InPath p (triple a t z) := by
      have hsel : InPath p (pair t z) := by
        rw [pair_comm]
        exact h.isolated_pair_selected z t (Ne.symm htz) hza hta hz
      have hneq : pair t z≠pair u v := by
        intro he
        have hb := congrArg (fun q : Vertex => q.val.testBit t.val) he
        simp [bit_pair,Ne.symm htz,Ne.symm htu,Ne.symm htv] at hb
      have hnl := h.other_not_low u v huv hua hva hu hv (pair t z) hsel (pair_nonzero t z htz) hneq
      have hcvr := endpoint_pair_neighbor_cover p a t z j htz hta hza h.cover hsel
        (fun k hka hkt hkz hkj => ⟨htp k hka hkt hkj,
          h.isolated_pair_selected z k (Ne.symm hkz) hza hka hz⟩)
      exact (force_two_neighbors p (pair t z) (triple a t z) (triple t z j) hnl hcvr).1
    exact ⟨one u hua htu hu,one v hva htv hv⟩
  have absent_matched (t : Coord) (hta : t≠a) (htu : t≠u) (htv : t≠v) :
      ¬ InPath p (pair a t) :=
    selected_pair_forbidden_two_triples p a t u v (Ne.symm hta) (Ne.symm hua) (Ne.symm hva)
      htu htv huv h.ha (triples t hta htu htv).1 (triples t hta htu htv).2
  obtain ⟨hj,hji⟩ := freshCoords_spec a u v
  let r := freshCoords a u v 0
  let s := freshCoords a u v 1
  have hrs : r≠s := by
    intro he
    have hc := hji 0 1 he
    exact (by decide : (0:Fin 4)≠1) hc
  have hr := triples r (hj 0).1 (hj 0).2.1 (hj 0).2.2
  have hs := triples s (hj 1).1 (hj 1).2.1 (hj 1).2.2
  have absent_u : ¬ InPath p (pair a u) := by
    apply selected_pair_forbidden_two_triples p a u r s (Ne.symm hua)
      (Ne.symm (hj 0).1) (Ne.symm (hj 1).1) (Ne.symm (hj 0).2.1) (Ne.symm (hj 1).2.1) hrs h.ha
    · simpa only [triple_swap a r u] using hr.1
    · simpa only [triple_swap a s u] using hs.1
  have absent_v : ¬ InPath p (pair a v) := by
    apply selected_pair_forbidden_two_triples p a v r s (Ne.symm hva)
      (Ne.symm (hj 0).1) (Ne.symm (hj 1).1) (Ne.symm (hj 0).2.2) (Ne.symm (hj 1).2.2) hrs h.ha
    · simpa only [triple_swap a r v] using hr.2
    · simpa only [triple_swap a s v] using hs.2
  have low_a : AtMostOneNeighbor p (unit a) := by
    have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (unit a) w) : w=0 := by
      obtain ⟨k,rfl⟩ := neighbor_unit a hadj
      by_cases hka : k=a
      · subst k; exact pair_self a
      by_cases hku : k=u
      · subst k; exact False.elim (absent_u hw)
      by_cases hkv : k=v
      · subst k; exact False.elim (absent_v hw)
      exact False.elim (absent_matched k hka hku hkv hw)
    intro x y hx hy hax hay
    exact (unique x hx hax).trans (unique y hy hay).symm
  apply h.other_not_low u v huv hua hva hu hv (unit a) h.ha (unit_nonzero a) _ low_a
  intro he
  have hb := congrArg (fun q : Vertex => q.val.testBit a.val) he
  simp [bit_unit,bit_pair,hua,hva] at hb

end EndpointMissingConfig
#print axioms EndpointMissingConfig.three_isolated_false
#print axioms EndpointMissingConfig.matching_false

end Snake9
