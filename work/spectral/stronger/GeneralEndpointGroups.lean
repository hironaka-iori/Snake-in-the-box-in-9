import GeneralGoodIndex

namespace Snake9
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def GoodEndpointResource (F : Finset (Finset Coord)) (a b c d i : Coord) (v : Vertex) : Prop :=
  v=triple a b i ∨
  (∃j : Coord, j≠a ∧ j≠b ∧ j≠c ∧ j≠d ∧ j≠i ∧ ({b,j} : Finset Coord)∈F ∧ v=pair j i) ∨
  (({b,d} : Finset Coord)∈F ∧ (v=pair c i ∨ v=pair d i)) ∨
  (({b,d} : Finset Coord)∉F ∧ ({d,i} : Finset Coord)∈F ∧ v=pair d i)

theorem good_resource_bit_self (F : Finset (Finset Coord)) (a b c d i : Coord)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    {v : Vertex} (hv : GoodEndpointResource F a b c d i v) : v.val.testBit i.val=true := by
  rcases hv with he | ⟨j,_,_,_,_,hji,_,he⟩ | ⟨_,he | he⟩ | ⟨_,_,he⟩ <;>
    subst v <;> simp_all [bit_pair,bit_triple,Ne.symm hia,Ne.symm hib,Ne.symm hic,Ne.symm hid]

theorem good_resource_bit_other (F : Finset (Finset Coord)) (a b c d i k : Coord)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d)
    (hik : i≠k) (hbk : ({b,k} : Finset Coord)∉F)
    {v : Vertex} (hv : GoodEndpointResource F a b c d i v) : v.val.testBit k.val=false := by
  rcases hv with he | ⟨j,_,_,_,_,_,hbj,he⟩ | ⟨_,he | he⟩ | ⟨_,_,he⟩
  · subst v; simp [bit_triple,Ne.symm hka,Ne.symm hkb,hik]
  · have hjk : j≠k := by intro he; subst j; exact hbk hbj
    subst v; simp [bit_pair,hjk,hik]
  · subst v; simp [bit_pair,Ne.symm hkc,hik]
  · subst v; simp [bit_pair,Ne.symm hkd,hik]
  · subst v; simp [bit_pair,Ne.symm hkd,hik]

theorem good_resource_isolated_extra_distinct (F : Finset (Finset Coord)) (a b c d i : Coord)
    (hab : a≠b) (had : a≠d) (hbc : b≠c) (hbd : b≠d)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    (hd : ∀s∈F,d∉s) {v : Vertex} (hv : GoodEndpointResource F a b c d i v) :
    v≠pair c i ∧ v≠triple a d i := by
  rcases hv with he | ⟨j,hja,hjb,hjc,hjd,hji,hbj,he⟩ | ⟨hbdF,_⟩ | ⟨_,hdiF,_⟩
  · subst v
    constructor <;> intro he <;>
      have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he <;>
      simp [bit_pair,bit_triple,hab,Ne.symm hbc,Ne.symm hbd,hib] at hb
  · subst v
    constructor
    · intro he
      rw [pair_comm j i,pair_comm c i] at he
      exact hjc (pair_injective_right i j c he)
    · intro he
      have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_pair,bit_triple,hja,hia,Ne.symm had] at hb
  · exact False.elim (hd _ hbdF (by simp))
  · exact False.elim (hd _ hdiF (by simp))

namespace OneTwoRoot
variable {m : Nat} {p : Snake m} {a b c d : Coord}
  (h : OneTwoRoot p a b c d) (f : MissingAtNeighbor p a c)
include h f

theorem good_selected_endpoint (i : Coord)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    (hbi : ({b,i} : Finset Coord)∉f.F)
    (hgood : ∀j, ({i,j} : Finset Coord)∈f.F→({b,j} : Finset Coord)∉f.F) :
    ∃v, InPath p v ∧ AtMostOneNeighbor p v ∧ GoodEndpointResource f.F a b c d i v := by
  have hci : InPath p (pair c i) := by
    apply h.selected_pair c i (Ne.symm hic) (Ne.symm h.hac) (Ne.symm h.hbc) hia hib
    simp [h.hcd,hid]
  have hdi : InPath p (pair d i) := by
    apply h.selected_pair d i (Ne.symm hid) (Ne.symm h.had) (Ne.symm h.hbd) hia hib
    simp [Ne.symm h.hcd,hic]
  rcases h.good_index_endpoint_alternative f i hia hib hic hid hbi hgood with
    ht | ⟨j,hja,hjb,hjc,hjd,hji,hbj,hl⟩ | ⟨hbd,hc | hd⟩ | ⟨hbd,hdiF,hl⟩
  · exact ⟨triple a b i,h.family_selected_t f i hia hib hic hbi,ht,Or.inl rfl⟩
  · refine ⟨pair j i,?_,hl,Or.inr (Or.inl ⟨j,hja,hjb,hjc,hjd,hji,hbj,rfl⟩)⟩
    apply h.selected_pair j i hji hja hjb hia hib
    simp [hjc,hjd]
  · exact ⟨pair c i,hci,hc,Or.inr (Or.inr (Or.inl ⟨hbd,Or.inl rfl⟩))⟩
  · exact ⟨pair d i,hdi,hd,Or.inr (Or.inr (Or.inl ⟨hbd,Or.inr rfl⟩))⟩
  · exact ⟨pair d i,hdi,hl,Or.inr (Or.inr (Or.inr ⟨hbd,hdiF,rfl⟩))⟩

theorem three_good_indices_false (j : Fin 3 → Coord) (hji : Function.Injective j)
    (hj : ∀r, j r≠a ∧ j r≠b ∧ j r≠c ∧ j r≠d ∧ ({b,j r} : Finset Coord)∉f.F ∧
      ∀k, ({j r,k} : Finset Coord)∈f.F→({b,k} : Finset Coord)∉f.F) : False := by
  classical
  have hex (r : Fin 3) := h.good_selected_endpoint f (j r) (hj r).1 (hj r).2.1 (hj r).2.2.1
    (hj r).2.2.2.1 (hj r).2.2.2.2.1 (hj r).2.2.2.2.2
  choose v hv hl hr using hex
  have hne (r s : Fin 3) (hrs : r≠s) : v r≠v s := by
    intro he
    have hsr : j s≠j r := fun he => hrs (hji he).symm
    have hs := good_resource_bit_other f.F a b c d (j s) (j r)
      (hj r).1 (hj r).2.1 (hj r).2.2.1 (hj r).2.2.2.1 hsr (hj r).2.2.2.2.1 (hr s)
    have ht := good_resource_bit_self f.F a b c d (j r)
      (hj r).1 (hj r).2.1 (hj r).2.2.1 (hj r).2.2.2.1 (hr r)
    rw [he,hs] at ht
    contradiction
  rcases three_low_degree_vertices_repeat p (hv 0) (hv 1) (hv 2) (hl 0) (hl 1) (hl 2) with he | he | he
  · exact hne 0 1 (by decide) he
  · exact hne 0 2 (by decide) he
  · exact hne 1 2 (by decide) he

theorem two_good_isolated_false (u v : Coord) (huv : u≠v)
    (hu : u≠a ∧ u≠b ∧ u≠c ∧ u≠d ∧ ({b,u} : Finset Coord)∉f.F ∧
      ∀k, ({u,k} : Finset Coord)∈f.F→({b,k} : Finset Coord)∉f.F)
    (hv : v≠a ∧ v≠b ∧ v≠c ∧ v≠d ∧ ({b,v} : Finset Coord)∉f.F ∧
      ∀k, ({v,k} : Finset Coord)∈f.F→({b,k} : Finset Coord)∉f.F)
    (hd : ∀s∈f.F,d∉s) (hiu : ∀s∈f.F,u∉s) : False := by
  obtain ⟨x,hx,hlx,hrx⟩ := h.good_selected_endpoint f u hu.1 hu.2.1 hu.2.2.1
    hu.2.2.2.1 hu.2.2.2.2.1 hu.2.2.2.2.2
  obtain ⟨y,hy,hly,hry⟩ := h.good_selected_endpoint f v hv.1 hv.2.1 hv.2.2.1
    hv.2.2.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2
  have hxy : x≠y := by
    intro he
    have hb := good_resource_bit_self f.F a b c d u hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hrx
    have hc := good_resource_bit_other f.F a b c d v u hu.1 hu.2.1 hu.2.2.1
      hu.2.2.2.1 (Ne.symm huv) hu.2.2.2.2.1 hry
    rw [he,hc] at hb
    contradiction
  have hxe := good_resource_isolated_extra_distinct f.F a b c d u h.hab h.had h.hbc h.hbd
    hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hd hrx
  have hye : y≠pair c u ∧ y≠triple a d u := by
    have hs := good_resource_bit_self f.F a b c d v hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hry
    constructor <;> intro he <;> rw [he] at hs <;>
      simp [bit_pair,bit_triple,Ne.symm hv.1,Ne.symm hv.2.2.1,Ne.symm hv.2.2.2.1,huv] at hs
  have hci : InPath p (pair c u) := by
    apply h.selected_pair c u (Ne.symm hu.2.2.1) (Ne.symm h.hac) (Ne.symm h.hbc) hu.1 hu.2.1
    simp [h.hcd,hu.2.2.2.1]
  have hadi : InPath p (triple a d u) := by
    apply (f.selected_iff d u (Ne.symm hu.2.2.2.1) (Ne.symm h.had) (Ne.symm h.hcd) hu.1 hu.2.2.1).mpr
    intro hm
    exact hd _ hm (by simp)
  rcases h.isolated_neighbor_pair_group f u hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hd hiu with hc | ha
  · rcases three_low_degree_vertices_repeat p hx hy hci hlx hly hc with he | he | he
    · exact hxy he
    · exact hxe.1 he
    · exact hye.1 he
  · rcases three_low_degree_vertices_repeat p hx hy hadi hlx hly ha with he | he | he
    · exact hxy he
    · exact hxe.2 he
    · exact hye.2 he

end OneTwoRoot
#print axioms OneTwoRoot.three_good_indices_false
#print axioms OneTwoRoot.two_good_isolated_false
end Snake9
