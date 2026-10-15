import SingletonAlphaBridge
import EndpointGroups
import FreshCoordinates
import CycleStructure

namespace Snake9
open SquareIncidence
set_option maxHeartbeats 600000
set_option maxRecDepth 100000

structure AdjacentConfig {m : Nat} (p : Snake m) (a b c d e : Coord) : Prop where
  hab : a≠b
  hac : a≠c
  hbc : b≠c
  had : a≠d
  hbd : b≠d
  hcd : c≠d
  hae : a≠e
  hbe : b≠e
  hce : c≠e
  ha : InPath p (unit a)
  hb : InPath p (unit b)
  hac_selected : InPath p (pair a c)
  cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b
  qcover : ∀ k : Coord, InPath (translate p (unit a)) (unit k) → k=a ∨ k=c
  forced : ForcedPairsExcept p c d
  qforced : ForcedPairsExcept (translate p (unit a)) b e

theorem translate_pair_membership {m : Nat} (p : Snake m) (a i j : Coord) :
    InPath (translate p (unit a)) (pair i j) ↔ InPath p (triple a i j) := by
  have he : vxor (unit a) (triple a i j) = pair i j := by
    apply Fin.ext
    change 2^a.val ^^^ ((2^a.val ^^^ 2^i.val) ^^^ 2^j.val) = 2^i.val ^^^ 2^j.val
    rw [Nat.xor_assoc, ← Nat.xor_assoc (2^a.val) (2^a.val), Nat.xor_self, Nat.zero_xor]
  rw [← he]
  exact inPath_translate_iff p (unit a) (triple a i j)

theorem translate_unit_membership {m : Nat} (p : Snake m) (a i : Coord) :
    InPath (translate p (unit a)) (unit i) ↔ InPath p (pair a i) := by
  have he : vxor (unit a) (pair a i) = unit i := vxor_cancel _ _
  rw [← he]
  exact inPath_translate_iff p (unit a) (pair a i)

namespace AdjacentConfig
variable {m : Nat} {p : Snake m} {a b c d e : Coord} (h : AdjacentConfig p a b c d e)
include h

theorem absent_unit (k : Coord) (hka : k≠a) (hkb : k≠b) : ¬ InPath p (unit k) := by
  intro hk
  rcases h.cover k hk with he | he
  · exact hka he
  · exact hkb he

theorem absent_second_unit (k : Coord) (hka : k≠a) (hkc : k≠c) :
    ¬ InPath (translate p (unit a)) (unit k) := by
  intro hk
  rcases h.qcover k hk with he | he
  · exact hka he
  · exact hkc he

theorem selected_pair (i j : Coord) (hij : i≠j)
    (hia : i≠a) (hib : i≠b) (hja : j≠a) (hjb : j≠b)
    (hnot : ¬ ((i=c ∧ j=d) ∨ (i=d ∧ j=c))) : InPath p (pair i j) :=
  h.forced i j hij (h.absent_unit i hia hib) (h.absent_unit j hja hjb) hnot

theorem selected_triple (i j : Coord) (hij : i≠j)
    (hia : i≠a) (hic : i≠c) (hja : j≠a) (hjc : j≠c)
    (hnot : ¬ ((i=b ∧ j=e) ∨ (i=e ∧ j=b))) : InPath p (triple a i j) :=
  (translate_pair_membership p a i j).mp
    (h.qforced i j hij (h.absent_second_unit i hia hic) (h.absent_second_unit j hja hjc) hnot)

theorem absent_pair_ak (k : Coord) (hka : k≠a) (hkc : k≠c) :
    ¬ InPath p (pair a k) := fun hk =>
  h.absent_second_unit k hka hkc ((translate_unit_membership p a k).mpr hk)

theorem absent_pair_bk (k : Coord) (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d) :
    ¬ InPath p (pair b k) := by
  intro hk
  have hr := arm_coordinate_in_missing p b a c d k (Ne.symm hkb) (Ne.symm hka)
    h.hb hk (fun x hx => (h.cover x hx).symm) h.forced
  rcases hr with he | he
  · exact hkc he
  · exact hkd he

theorem absent_triple_ack (k : Coord) (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hke : k≠e) :
    ¬ InPath p (triple a c k) := by
  intro hk
  have hc : InPath (translate p (unit a)) (unit c) :=
    (translate_unit_membership p a c).mpr h.hac_selected
  have hck := (translate_pair_membership p a c k).mpr hk
  have hr := arm_coordinate_in_missing (translate p (unit a)) c a b e k
    (Ne.symm hkc) (Ne.symm hka) hc hck (fun x hx => (h.qcover x hx).symm) h.qforced
  rcases hr with he | he
  · exact hkb he
  · exact hke he
end AdjacentConfig

#print axioms translate_pair_membership
#print axioms AdjacentConfig.absent_triple_ack
end Snake9
