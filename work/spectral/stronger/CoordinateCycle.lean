import CycleStructure
import CubeCoordinateAlgebra

namespace Snake9
set_option maxHeartbeats 1000000

theorem selected_coordinate_cycle8_false {m : Nat} (p : Snake m)
    (a b c d k : Coord)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hak : a ≠ k)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbk : b ≠ k)
    (hcd : c ≠ d) (hck : c ≠ k) (hdk : d ≠ k)
    (s0 : InPath p (triple a b k))
    (s1 : InPath p (quad a b c k))
    (s2 : InPath p (triple b c k))
    (s3 : InPath p (pair c k))
    (s4 : InPath p (triple c d k))
    (s5 : InPath p (pair d k))
    (s6 : InPath p (triple a d k))
    (s7 : InPath p (quad a b d k)) : False := by
  apply selected_cycle8_false p _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7
  · have he : quad a b c k = vxor (triple a b k) (unit c) := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    rw [he]
    exact adj_flip _ _
  · apply adj_symmetric
    have he : quad a b c k = vxor (triple b c k) (unit a) := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    rw [he]
    exact adj_flip _ _
  · apply adj_symmetric
    have he : triple b c k = vxor (pair c k) (unit b) := by
      apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
    rw [he]
    exact adj_flip _ _
  · have he : triple c d k = vxor (pair c k) (unit d) := by
      apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
    rw [he]
    exact adj_flip _ _
  · apply adj_symmetric
    have he : triple c d k = vxor (pair d k) (unit c) := by
      apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
    rw [he]
    exact adj_flip _ _
  · have he : triple a d k = vxor (pair d k) (unit a) := by
      apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
    rw [he]
    exact adj_flip _ _
  · have he : quad a b d k = vxor (triple a d k) (unit b) := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    rw [he]
    exact adj_flip _ _
  · apply adj_symmetric
    have he : quad a b d k = vxor (triple a b k) (unit d) := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    rw [he]
    exact adj_flip _ _
  · intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit d.val) he
    simp [hab,hac,had,hak,hbc,hbd,hbk,hcd,hck,hdk,Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hak,Ne.symm hbc,Ne.symm hbd,Ne.symm hbk,Ne.symm hcd,Ne.symm hck,Ne.symm hdk] at hb
  · intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [hab,hac,had,hak,hbc,hbd,hbk,hcd,hck,hdk,Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hak,Ne.symm hbc,Ne.symm hbd,Ne.symm hbk,Ne.symm hcd,Ne.symm hck,Ne.symm hdk] at hb
  · intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [hab,hac,had,hak,hbc,hbd,hbk,hcd,hck,hdk,Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hak,Ne.symm hbc,Ne.symm hbd,Ne.symm hbk,Ne.symm hcd,Ne.symm hck,Ne.symm hdk] at hb
  · intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit b.val) he
    simp [hab,hac,had,hak,hbc,hbd,hbk,hcd,hck,hdk,Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hak,Ne.symm hbc,Ne.symm hbd,Ne.symm hbk,Ne.symm hcd,Ne.symm hck,Ne.symm hdk] at hb
  · intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit c.val) he
    simp [hab,hac,had,hak,hbc,hbd,hbk,hcd,hck,hdk,Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hak,Ne.symm hbc,Ne.symm hbd,Ne.symm hbk,Ne.symm hcd,Ne.symm hck,Ne.symm hdk] at hb
  · intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit c.val) he
    simp [hab,hac,had,hak,hbc,hbd,hbk,hcd,hck,hdk,Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hak,Ne.symm hbc,Ne.symm hbd,Ne.symm hbk,Ne.symm hcd,Ne.symm hck,Ne.symm hdk] at hb
  · intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [hab,hac,had,hak,hbc,hbd,hbk,hcd,hck,hdk,Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hak,Ne.symm hbc,Ne.symm hbd,Ne.symm hbk,Ne.symm hcd,Ne.symm hck,Ne.symm hdk] at hb
  · intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit d.val) he
    simp [hab,hac,had,hak,hbc,hbd,hbk,hcd,hck,hdk,Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hak,Ne.symm hbc,Ne.symm hbd,Ne.symm hbk,Ne.symm hcd,Ne.symm hck,Ne.symm hdk] at hb

#print axioms selected_coordinate_cycle8_false
end Snake9
