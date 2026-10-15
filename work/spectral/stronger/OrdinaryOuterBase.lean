import EqualOuterPairBase

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

structure OrdinaryOuterConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  outer : DistinctOuterConfig p a b c d
  A : Finset Coord
  B : Finset Coord
  Acard : A.card=2
  Bcard : B.card=2
  Asub : A⊆distinctR a b c d
  Bsub : B⊆distinctR a b c d
  hne : A≠B
  left_eq : outer.left.F={{b,d},A}
  right_eq : outer.right.F={{a,c},B}

def OrdinaryHoleGood (F : Finset (Finset Coord)) (R : Finset Coord)
    (c d : Coord) (A B : Finset Coord) : Prop :=
  A∉F ∧ (∀s∈A,({c,s}:Finset Coord)∉F ∧ ({d,s}:Finset Coord)∉F) ∧
    ∀r∈R,r∉A → ¬∀s∈A,({s,r}:Finset Coord)∈F ∨ ({s,r}:Finset Coord)=B

theorem pair_ne_of_outside {R E : Finset Coord} (hE : E⊆R) (x y : Coord) (hx : x∉R) :
    ({x,y}:Finset Coord)≠E := by
  intro he
  exact hx (hE (he ▸ (by simp : x∈({x,y}:Finset Coord))))

namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem left_pair_iff (x y : Coord) (hx : x∈distinctR a b c d)
    (hy : y∈distinctR a b c d) (hxy : x≠y) :
    InPath p (pair x y) ↔ ({x,y}:Finset Coord)≠h.A := by
  have hhx := (mem_distinctR a b c d x).mp hx
  have hhy := (mem_distinctR a b c d y).mp hy
  rw [h.outer.left.selected_iff x y hxy hhx.1 hhx.2.2.1 hhy.1 hhy.2.2.1,h.left_eq]
  simp only [mem_insert,mem_singleton,not_or]
  exact and_iff_right (delta_pair_ne x y b d hhx.2.1 hhx.2.2.2)

theorem right_pair_iff (x y : Coord) (hx : x∈distinctR a b c d)
    (hy : y∈distinctR a b c d) (hxy : x≠y) :
    InPath p (quad a b x y) ↔ ({x,y}:Finset Coord)≠h.B := by
  have hhx := (mem_distinctR a b c d x).mp hx
  have hhy := (mem_distinctR a b c d y).mp hy
  rw [h.outer.right_pair_iff x y hxy hhx.2.1 hhx.2.2.2 hhy.2.1 hhy.2.2.2,h.right_eq]
  simp only [mem_insert,mem_singleton,not_or]
  exact and_iff_right (delta_pair_ne x y a c hhx.1 hhx.2.2.1)

theorem row_selected (k : Coord) (hk : k∈distinctR a b c d) : InPath p (pair b k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  apply (h.outer.left.selected_iff b k (Ne.symm hh.2.1) (Ne.symm h.outer.hab)
    h.outer.hbc hh.1 hh.2.2.1).mpr
  rw [h.left_eq]
  simp only [mem_insert,mem_singleton,not_or]
  exact ⟨delta_pair_ne_right b k b d hh.2.1 hh.2.2.2,
    pair_ne_of_outside h.Asub b k (by simp [distinctR])⟩

theorem side_pair (k : Coord) (hk : k∈distinctR a b c d) : InPath p (pair d k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  apply (h.outer.left.selected_iff d k (Ne.symm hh.2.2.2) (Ne.symm h.outer.had)
    (Ne.symm h.outer.hcd) hh.1 hh.2.2.1).mpr
  rw [h.left_eq]
  simp only [mem_insert,mem_singleton,not_or]
  exact ⟨delta_pair_ne_right d k b d hh.2.1 hh.2.2.2,
    pair_ne_of_outside h.Asub d k (by simp [distinctR])⟩

theorem side_quad (k : Coord) (hk : k∈distinctR a b c d) : InPath p (quad a b c k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  apply (h.outer.right_pair_iff c k (Ne.symm hh.2.2.1) (Ne.symm h.outer.hbc)
    h.outer.hcd hh.2.1 hh.2.2.2).mpr
  rw [h.right_eq]
  simp only [mem_insert,mem_singleton,not_or]
  exact ⟨delta_pair_ne_right c k a c hh.1 hh.2.2.1,
    pair_ne_of_outside h.Bsub c k (by simp [distinctR])⟩

def mirror : OrdinaryOuterConfig (translate p (pair a b)) b a d c where
  outer := h.outer.mirror
  A := h.B
  B := h.A
  Acard := h.Bcard
  Bcard := h.Acard
  Asub := by
    intro x hx
    have hh := (mem_distinctR a b c d x).mp (h.Bsub hx)
    exact (mem_distinctR b a d c x).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  Bsub := by
    intro x hx
    have hh := (mem_distinctR a b c d x).mp (h.Asub hx)
    exact (mem_distinctR b a d c x).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  hne := Ne.symm h.hne
  left_eq := h.right_eq
  right_eq := h.left_eq

theorem absent_pair_a (k : Coord) (hka : k≠a) (hkb : k≠b) : ¬InPath p (pair a k) := by
  let q : LocalDenseRows p a b c d := ⟨h.outer,∅,by simp⟩
  exact q.absent_middle_pair k hka hkb

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.left_pair_iff
#print axioms OrdinaryOuterConfig.absent_pair_a
end
end Snake9
