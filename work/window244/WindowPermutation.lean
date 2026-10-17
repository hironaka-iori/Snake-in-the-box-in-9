import WindowAlpha
import CubeCoordinateAlgebra
import Mathlib.Data.Fintype.EquivFin

namespace Snake9.Window244
open SquareIncidence
noncomputable section
local instance propDecPermutation (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000

def bits (v : Vertex) (a : Coord) : Bool := v.val.testBit a.val

theorem bits_injective : Function.Injective bits := by
  intro u v h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 9
  · exact congrFun h ⟨k,hk⟩
  · have hp : 512 ≤ 2^k := by
      have h9 : 9 ≤ k := by omega
      exact Nat.pow_le_pow_right (by decide : 0 < 2) h9
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le u.isLt hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le v.isLt hp)]

def bitsEquiv : Vertex ≃ (Coord → Bool) := Equiv.ofBijective bits
  ((Fintype.bijective_iff_injective_and_card bits).mpr
    ⟨bits_injective,by simp [Vertex,Coord]⟩)

def permuteVertex (σ : Equiv.Perm Coord) (v : Vertex) : Vertex :=
  bitsEquiv.symm (fun k => bits v (σ.symm k))

theorem permute_bits (σ : Equiv.Perm Coord) (v : Vertex) (k : Coord) :
    bits (permuteVertex σ v) k = bits v (σ.symm k) := by
  exact congrFun (bitsEquiv.apply_symm_apply (fun k => bits v (σ.symm k))) k

theorem permute_inverse (σ : Equiv.Perm Coord) (v : Vertex) :
    permuteVertex σ.symm (permuteVertex σ v) = v := by
  apply bits_injective
  funext k
  simp only [permute_bits,Equiv.symm_symm,Equiv.symm_apply_apply]

def permuteVertexEquiv (σ : Equiv.Perm Coord) : Vertex ≃ Vertex where
  toFun := permuteVertex σ
  invFun := permuteVertex σ.symm
  left_inv := permute_inverse σ
  right_inv v := by simpa using permute_inverse σ.symm v

theorem bits_flip (v : Vertex) (a k : Coord) :
    bits (flip a v) k = (bits v k ^^ decide (a=k)) := by
  simp only [bits,SquareIncidence.flip,vxor,Nat.testBit_xor,bit_unit]

theorem permute_flip (σ : Equiv.Perm Coord) (v : Vertex) (a : Coord) :
    permuteVertex σ (flip a v) = flip (σ a) (permuteVertex σ v) := by
  apply bits_injective
  funext k
  rw [permute_bits,bits_flip,bits_flip,permute_bits]
  have he : (a = σ.symm k) ↔ (σ a = k) := by
    constructor
    · intro h; rw [h]; exact σ.apply_symm_apply k
    · intro h; rw [←h]; exact (σ.symm_apply_apply a).symm
  simp only [he]

theorem permute_adj_forward (σ : Equiv.Perm Coord) (u v : Vertex) (h : Adj u v) :
    Adj (permuteVertex σ u) (permuteVertex σ v) := by
  obtain ⟨a,ha,he⟩ := (adj_iff_coordinate_flip u v).mp h
  have hv : v = flip ⟨a,ha⟩ u := Fin.ext he
  rw [hv,permute_flip]
  exact flip_adj _ _

theorem permute_adj (σ : Equiv.Perm Coord) (u v : Vertex) :
    Adj (permuteVertex σ u) (permuteVertex σ v) ↔ Adj u v := by
  constructor
  · intro h
    have hh := permute_adj_forward σ.symm _ _ h
    simpa only [permute_inverse] using hh
  · exact permute_adj_forward σ u v

def permuteSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) : Snake m where
  vertex i := permuteVertex σ (p.vertex i)
  distinct i j h := p.distinct i j ((permuteVertexEquiv σ).injective h)
  induced i j hij := by rw [permute_adj]; exact p.induced i j hij

theorem inPath_permute_iff {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (v : Vertex) :
    InPath (permuteSnake σ p) (permuteVertex σ v) ↔ InPath p v := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,(permuteVertexEquiv σ).injective hi⟩
  · rintro ⟨i,rfl⟩
    exact ⟨i,rfl⟩

theorem permute_zero (σ : Equiv.Perm Coord) : permuteVertex σ 0 = 0 := by
  apply bits_injective
  funext k
  rw [permute_bits]
  simp [bits]

theorem permute_unit (σ : Equiv.Perm Coord) (a : Coord) :
    permuteVertex σ (unit a) = unit (σ a) := by
  have hz (a : Coord) : flip a 0 = unit a := by
    apply Fin.ext; exact Nat.zero_xor _
  rw [←hz a,permute_flip,permute_zero,hz]

def sortPair (a b : Coord) (hne : a ≠ b) : AxisPair :=
  if h : a.val < b.val then ⟨(a,b),h⟩ else
    ⟨(b,a),by change b.val < a.val; have : a.val ≠ b.val := fun he => hne (Fin.ext he); omega⟩

theorem sortPair_comm (a b : Coord) (hne : a ≠ b) :
    sortPair a b hne = sortPair b a hne.symm := by
  unfold sortPair
  split_ifs with h1 h2 h2
  · omega
  · rfl
  · rfl
  · have : a.val ≠ b.val := fun he => hne (Fin.ext he)
    omega

theorem sortPair_existing (ab : AxisPair) :
    sortPair ab.val.1 ab.val.2 (fun h => (ne_of_lt ab.property) (congrArg Fin.val h)) = ab := by
  simp only [sortPair,dif_pos ab.property]

def axisPermute (σ : Equiv.Perm Coord) (ab : AxisPair) : AxisPair :=
  sortPair (σ ab.val.1) (σ ab.val.2)
    (fun h => (ne_of_lt ab.property) (congrArg Fin.val (σ.injective h)))

theorem axisPermute_sortPair (σ : Equiv.Perm Coord) (a b : Coord) (hne : a ≠ b) :
    axisPermute σ (sortPair a b hne) = sortPair (σ a) (σ b) (fun h => hne (σ.injective h)) := by
  by_cases hlt : a.val < b.val
  · have h : sortPair a b hne = ⟨(a,b),hlt⟩ := dif_pos hlt
    rw [h]; rfl
  · have hgt : b.val < a.val := by
      have : a.val ≠ b.val := fun he => hne (Fin.ext he)
      omega
    have h : sortPair a b hne = ⟨(b,a),hgt⟩ := dif_neg hlt
    rw [h]
    exact sortPair_comm (σ b) (σ a) _

theorem axisPermute_inverse (σ : Equiv.Perm Coord) (ab : AxisPair) :
    axisPermute σ.symm (axisPermute σ ab) = ab := by
  change axisPermute σ.symm (sortPair (σ ab.val.1) (σ ab.val.2) _) = ab
  rw [axisPermute_sortPair]
  simpa only [Equiv.symm_apply_apply] using sortPair_existing ab

def axisPermuteEquiv (σ : Equiv.Perm Coord) : AxisPair ≃ AxisPair where
  toFun := axisPermute σ
  invFun := axisPermute σ.symm
  left_inv := axisPermute_inverse σ
  right_inv ab := by simpa using axisPermute_inverse σ.symm ab

theorem singleton_sortPair {m : Nat} (p : Snake m) (v : Vertex) (a b : Coord) (hne : a ≠ b) :
    SquareIncidence.singleton p (sortPair a b hne) v =
      if InPath p v ∧ ¬ InPath p (flip a v) ∧ ¬ InPath p (flip b v) ∧
         ¬ InPath p (flip b (flip a v)) then 1 else 0 := by
  classical
  by_cases hlt : a.val < b.val
  · simp only [sortPair,dif_pos hlt,SquareIncidence.singleton]
  · simp only [sortPair,dif_neg hlt,SquareIncidence.singleton]
    rw [flip_commute a b v]
    congr 1
    apply propext
    tauto

theorem singleton_permute {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m)
    (v : Vertex) (ab : AxisPair) :
    SquareIncidence.singleton (permuteSnake σ p) (axisPermute σ ab) (permuteVertex σ v) =
      SquareIncidence.singleton p ab v := by
  unfold axisPermute
  rw [singleton_sortPair]
  unfold SquareIncidence.singleton
  simp only [←permute_flip,inPath_permute_iff]

theorem localAlpha_permute {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m)
    (i : Fin (m+1)) : localAlpha (permuteSnake σ p) i = localAlpha p i := by
  unfold localAlpha
  calc
    _ = ∑ ab : AxisPair, SquareIncidence.singleton (permuteSnake σ p)
        (axisPermuteEquiv σ ab) (permuteVertex σ (p.vertex i)) :=
      (Equiv.sum_comp (axisPermuteEquiv σ) (fun ab =>
        SquareIncidence.singleton (permuteSnake σ p) ab (permuteVertex σ (p.vertex i)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ab _
      exact singleton_permute σ p _ ab

#print axioms bits_injective
#print axioms permute_adj
#print axioms inPath_permute_iff
#print axioms permute_unit
#print axioms axisPermute_inverse
#print axioms localAlpha_permute
end
end Snake9.Window244
