import OrdinaryOuterBase
import CommonHoleEndpointGroups

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section

def ordinaryHoleVertex (a : Coord) (H : Finset Coord) : Vertex :=
  vxor (unit a) (edgeVertex H)

theorem ordinaryHoleVertex_pair (a i j : Coord) (hij : i≠j) :
    ordinaryHoleVertex a {i,j}=triple a i j := by
  simp only [ordinaryHoleVertex,edgeVertex_pair i j hij,triple,pair,vxor_assoc]

theorem ordinaryHoleVertex_injective (a : Coord) (H K : Finset Coord)
    (hH : H.card=2) (hK : K.card=2) (he : ordinaryHoleVertex a H=ordinaryHoleVertex a K) : H=K := by
  apply edgeVertex_injective_on_pairs H K hH hK
  have hh := congrArg (vxor (unit a)) he
  simpa only [ordinaryHoleVertex,vxor_cancel] using hh

theorem ordinaryHoleVertex_bits {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : DistinctOuterConfig p a b c d) (H : Finset Coord) (hH : H.card=2)
    (hHR : H⊆distinctR a b c d) :
    (ordinaryHoleVertex a H).val.testBit a.val=true ∧
    (ordinaryHoleVertex a H).val.testBit b.val=false ∧
    (ordinaryHoleVertex a H).val.testBit c.val=false ∧
    (ordinaryHoleVertex a H).val.testBit d.val=false := by
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hH
  have hi := (mem_distinctR a b c d i).mp (hHR (by simp))
  have hj := (mem_distinctR a b c d j).mp (hHR (by simp))
  rw [ordinaryHoleVertex_pair a i j hij]
  simp [bit_triple,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2,
    hj.1,hj.2.1,hj.2.2.1,hj.2.2.2,h.hab,h.hac,h.had]

theorem active_ne_ordinaryHoleVertex {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : DistinctOuterConfig p a b c d) (H : Finset Coord) (hH : H.card=2)
    (hHR : H⊆distinctR a b c d) (k : Coord) (hk : k∈distinctR a b c d)
    (v : Vertex) (hv : ActiveEndpointMember a b c d k v) : v≠ordinaryHoleVertex a H := by
  have hb := ordinaryHoleVertex_bits h H hH hHR
  have hh := (mem_distinctR a b c d k).mp hk
  intro he
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · have hx := hb.1
    rw [←he] at hx
    simp [bit_pair,Ne.symm h.hab,hh.1] at hx
  · have hx := hb.2.2.1
    rw [←he] at hx
    simp [bit_triple,h.hac,hh.2.2.1] at hx
  · have hx := hb.2.2.2
    rw [←he] at hx
    simp [bit_triple,h.had,hh.2.2.2] at hx
  · have hx := hb.1
    rw [←he] at hx
    simp [bit_pair,Ne.symm h.had,hh.1] at hx
  · have hx := hb.2.1
    rw [←he] at hx
    simp [bit_quad,h.hab,Ne.symm h.hbc,hh.2.1] at hx

#print axioms ordinaryHoleVertex_bits
#print axioms active_ne_ordinaryHoleVertex
end
end Snake9
