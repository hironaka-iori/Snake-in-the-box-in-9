import CommonHoleBase

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Dense ordinary corners and four active rows; exact exceptional families are not required. -/
structure DenseOuterConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  outer : DistinctOuterConfig p a b c d
  e : Coord
  he : e≠a ∧ e≠b ∧ e≠c ∧ e≠d
  ordinary_corners : ∀i j,i∈distinctR a b c d → j∈distinctR a b c d → i≠j →
    InPath p (pair i j) ∧ InPath p (quad a b i j)
  active_corners : ∀k,k∈distinctR a b c d → k≠e →
    InPath p (pair b k) ∧ InPath p (pair d k) ∧ InPath p (quad a b c k)

namespace DenseOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : DenseOuterConfig p a b c d)
include h

theorem row_cover (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e)
    (w : Vertex) (hw : InPath p w) (hadj : Adj (pair b k) w) :
    w=triple b k c ∨ w=triple b k d := by
  rcases h.outer.row_neighbor_cover k hk w hw hadj with he | he | ⟨l,hl,hlk,he⟩
  · exact Or.inl he
  · exact Or.inr he
  · have hh := (mem_distinctR a b c d k).mp hk
    have hh' := (mem_distinctR a b c d l).mp hl
    have hs := h.ordinary_corners k l hk hl (Ne.symm hlk)
    exact False.elim (middle_row_triple_forbidden p a b k l h.outer.hab
      (Ne.symm hh.1) (Ne.symm hh'.1) (Ne.symm hh.2.1) (Ne.symm hh'.2.1)
      (Ne.symm hlk) (h.active_corners k hk hke).1 hs.1 hs.2 (he ▸ hw))

theorem active_middle_selected (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s) :
    InPath p (triple a c k) ∧ InPath p (triple a d k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  constructor
  · apply (f.selected_iff c k (Ne.symm hkc) (Ne.symm h.outer.hac)
      (Ne.symm h.outer.hbc) hka hkb).mpr
    intro hm; exact hisol _ hm (by simp)
  · apply (f.selected_iff d k (Ne.symm hkd) (Ne.symm h.outer.had)
      (Ne.symm h.outer.hbd) hka hkb).mpr
    intro hm; exact hisol _ hm (by simp)

end DenseOuterConfig

def CommonHoleConfig.toDense {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : CommonHoleConfig p a b c d) : DenseOuterConfig p a b c d where
  outer := h.outer
  e := h.e
  he := h.he
  ordinary_corners := h.ordinary_corners
  active_corners := h.active_corners

#print axioms CommonHoleConfig.toDense
end
end Snake9