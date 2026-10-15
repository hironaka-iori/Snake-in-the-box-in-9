import OrdinaryOuterHoleEndpoints
import OrdinaryPairEndpoints

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section

structure SharedOuterConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  ordinary : OrdinaryOuterConfig p a b c d
  e : Coord
  x : Coord
  y : Coord
  he : e∈distinctR a b c d
  hx : x∈distinctR a b c d
  hy : y∈distinctR a b c d
  hex : e≠x
  hey : e≠y
  hxy : x≠y
  Aeq : ordinary.A={e,x}
  Beq : ordinary.B={e,y}

namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)

def mirror : SharedOuterConfig (translate p (pair a b)) b a d c where
  ordinary := h.ordinary.mirror
  e := h.e
  x := h.y
  y := h.x
  he := by
    have hh := (mem_distinctR a b c d h.e).mp h.he
    exact (mem_distinctR b a d c h.e).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  hx := by
    have hh := (mem_distinctR a b c d h.y).mp h.hy
    exact (mem_distinctR b a d c h.y).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  hy := by
    have hh := (mem_distinctR a b c d h.x).mp h.hx
    exact (mem_distinctR b a d c h.x).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  hex := h.hey
  hey := h.hex
  hxy := Ne.symm h.hxy
  Aeq := h.Beq
  Beq := h.Aeq

end SharedOuterConfig
#print axioms SharedOuterConfig.mirror
end
end Snake9
