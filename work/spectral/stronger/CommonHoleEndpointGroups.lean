import CommonHoleCounting
import CommonHolePairs
import CommonHoleIsolated

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

def ActiveEndpointMember (a b c d k : Coord) (v : Vertex) : Prop :=
  v=pair b k ∨ v=triple a c k ∨ v=triple a d k ∨ v=pair d k ∨ v=quad a b c k

theorem active_endpoint_bit (a b c d k : Coord) (hk : k∈distinctR a b c d)
    (v : Vertex) (hv : ActiveEndpointMember a b c d k v) : v.val.testBit k.val=true := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  rcases hv with rfl | rfl | rfl | rfl | rfl <;>
    simp [bit_pair,bit_triple,bit_quad,Ne.symm hka,Ne.symm hkb,Ne.symm hkc,Ne.symm hkd]

theorem active_endpoint_other_bit (a b c d k l : Coord) (hk : k∈distinctR a b c d)
    (hkl : k≠l) (v : Vertex) (hv : ActiveEndpointMember a b c d l v) : v.val.testBit k.val=false := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  rcases hv with rfl | rfl | rfl | rfl | rfl <;>
    simp [bit_pair,bit_triple,bit_quad,Ne.symm hka,Ne.symm hkb,Ne.symm hkc,Ne.symm hkd,Ne.symm hkl]

theorem active_endpoint_groups_disjoint (a b c d k l : Coord) (hk : k∈distinctR a b c d)
    (hkl : k≠l) (v w : Vertex) (hv : ActiveEndpointMember a b c d k v)
    (hw : ActiveEndpointMember a b c d l w) : v≠w := by
  intro he
  have hb := congrArg (fun x : Vertex => x.val.testBit k.val) he
  change v.val.testBit k.val=w.val.testBit k.val at hb
  rw [active_endpoint_bit a b c d k hk v hv,
    active_endpoint_other_bit a b c d k l hk hkl w hw] at hb
  cases hb

theorem three_active_endpoint_groups_false {m : Nat} (p : Snake m) (a b c d : Coord)
    (j : Fin 3 → Coord) (hinj : Function.Injective j) (hj : ∀r,j r∈distinctR a b c d)
    (hep : ∀r,∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d (j r) v) : False := by
  obtain ⟨u,hu,hlu,hgu⟩ := hep 0
  obtain ⟨v,hv,hlv,hgv⟩ := hep 1
  obtain ⟨w,hw,hlw,hgw⟩ := hep 2
  have h01 : j 0≠j 1 := fun he => (by decide : (0:Fin 3)≠1) (hinj he)
  have h02 : j 0≠j 2 := fun he => (by decide : (0:Fin 3)≠2) (hinj he)
  have h12 : j 1≠j 2 := fun he => (by decide : (1:Fin 3)≠2) (hinj he)
  rcases three_low_degree_vertices_repeat p hu hv hw hlu hlv hlw with he | he | he
  · exact active_endpoint_groups_disjoint a b c d _ _ (hj 0) h01 u v hgu hgv he
  · exact active_endpoint_groups_disjoint a b c d _ _ (hj 0) h02 u w hgu hgw he
  · exact active_endpoint_groups_disjoint a b c d _ _ (hj 1) h12 v w hgv hgw he

namespace CommonHoleConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : CommonHoleConfig p a b c d)
include h

theorem isolated_active_endpoint (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (his : PairIsolated f.F k) :
    ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v := by
  have hs := h.active_corners k hk hke
  have ht := h.toDense.active_middle_selected f k hk his
  rcases h.toDense.isolated_endpoint_group f k hk hke his with hl | hl | hl
  · exact ⟨pair b k,hs.1,hl,Or.inl rfl⟩
  · exact ⟨triple a c k,ht.1,hl,Or.inr (Or.inl rfl)⟩
  · exact ⟨triple a d k,ht.2,hl,Or.inr (Or.inr (Or.inl rfl))⟩

theorem three_isolated_active_false (f : MissingAtNeighbor p a b)
    (j : Fin 3 → Coord) (hinj : Function.Injective j)
    (hj : ∀r,j r∈distinctR a b c d ∧ j r≠h.e ∧ PairIsolated f.F (j r)) : False := by
  exact three_active_endpoint_groups_false p a b c d j hinj (fun r => (hj r).1)
    (fun r => h.isolated_active_endpoint f (j r) (hj r).1 (hj r).2.1 (hj r).2.2)

theorem ordinary_pair_and_isolated_false (f : MissingAtNeighbor p a b)
    (i j k : Coord) (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d)
    (hij : i≠j) (hm : ({i,j}:Finset Coord)∈f.F)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (his : PairIsolated f.F k) : False := by
  have hs := h.ordinary_corners i j hi hj hij
  have hl0 := h.missing_ordinary_pair_low f i j hi hj hij hm
  have hl1 := h.missing_ordinary_quad_low f i j hi hj hij hm
  obtain ⟨v,hv,hlv,hgroup⟩ := h.isolated_active_endpoint f k hk hke his
  have hki : k≠i := by intro he; exact his {i,j} hm (by simp [he])
  have hkj : k≠j := by intro he; exact his {i,j} hm (by simp [he])
  have hks := (mem_distinctR a b c d k).mp hk
  have his' := (mem_distinctR a b c d i).mp hi
  have hjs' := (mem_distinctR a b c d j).mp hj
  have hne : pair i j≠quad a b i j := by
    intro he
    have hb := congrArg (fun x : Vertex => x.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.outer.hab,his'.1,hjs'.1] at hb
  have hn0 : v≠pair i j := by
    intro he
    have hb := active_endpoint_bit a b c d k hk v hgroup
    rw [he] at hb
    simp [bit_pair,Ne.symm hki,Ne.symm hkj] at hb
  have hn1 : v≠quad a b i j := by
    intro he
    have hb := active_endpoint_bit a b c d k hk v hgroup
    rw [he] at hb
    simp [bit_quad,Ne.symm hks.1,Ne.symm hks.2.1,Ne.symm hki,Ne.symm hkj] at hb
  rcases three_low_degree_vertices_repeat p hs.1 hs.2 hv hl0 hl1 hlv with he | he | he
  · exact hne he
  · exact hn0 he.symm
  · exact hn1 he.symm

theorem two_ordinary_missing_false (f : MissingAtNeighbor p a b)
    (i j k l : Coord) (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d)
    (hk : k∈distinctR a b c d) (hl : l∈distinctR a b c d)
    (hij : i≠j) (hkl : k≠l)
    (hm : ({i,j}:Finset Coord)∈f.F) (hn : ({k,l}:Finset Coord)∈f.F)
    (hne : ({i,j}:Finset Coord)≠{k,l}) : False := by
  have hs := h.ordinary_corners i j hi hj hij
  have ht := (h.ordinary_corners k l hk hl hkl).1
  have hl0 := h.missing_ordinary_pair_low f i j hi hj hij hm
  have hl1 := h.missing_ordinary_quad_low f i j hi hj hij hm
  have hl2 := h.missing_ordinary_pair_low f k l hk hl hkl hn
  have hi' := (mem_distinctR a b c d i).mp hi
  have hj' := (mem_distinctR a b c d j).mp hj
  have hk' := (mem_distinctR a b c d k).mp hk
  have hl' := (mem_distinctR a b c d l).mp hl
  rcases three_low_degree_vertices_repeat p hs.1 hs.2 ht hl0 hl1 hl2 with he | he | he
  · have hb := congrArg (fun x : Vertex => x.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.outer.hab,hi'.1,hj'.1] at hb
  · exact hne (pair_vertex_eq_support i j k l hij hkl he)
  · have hb := congrArg (fun x : Vertex => x.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.outer.hab,hi'.1,hj'.1,hk'.1,hl'.1] at hb

end CommonHoleConfig
#print axioms three_active_endpoint_groups_false
#print axioms CommonHoleConfig.ordinary_pair_and_isolated_false
#print axioms CommonHoleConfig.two_ordinary_missing_false
end
end Snake9
