import Std

/-!
General parallel-edge argument and the saved source. Compilation receipts are separate.

The generic result allows every coordinate map, including nonbijective maps.
The concrete obstruction is linked below to the literal saved99-vertex array.

Once those identities are established, reversal would impose the prohibited
four image equations. This file makes no setwise-stabilizer classification.
-/

namespace ParallelEdges207

universe u

abbrev Word (I : Type u) := I → Bool

def difference {I : Type u} (x y : Word I) : Word I :=
  fun i => Bool.xor (x i) (y i)

def affine {I : Type u} (pi : I → I) (b : Word I) (x : Word I) : Word I :=
  fun i => Bool.xor (x (pi i)) (b i)

theorem xor_cancel_right (x y c : Bool) :
    Bool.xor (Bool.xor x c) (Bool.xor y c) = Bool.xor x y := by
  cases x <;> cases y <;> cases c <;> rfl

/-- Translation cancels from the difference word; the remaining action is
coordinate pullback. No injectivity or surjectivity of `pi` is needed. -/
theorem difference_affine {I : Type u} (pi : I → I) (b x y : Word I) :
    difference (affine pi b x) (affine pi b y) =
      (fun i => difference x y (pi i)) := by
  funext i
  exact xor_cancel_right (x (pi i)) (y (pi i)) (b i)

/-- Equal edge-difference words remain equal under every coordinate-affine
map. This implication also applies to pairs that are not edges. -/
theorem parallel_preserved {I : Type u} (pi : I → I) (b : Word I)
    (x₀ x₁ y₀ y₁ : Word I)
    (h : difference x₀ x₁ = difference y₀ y₁) :
    difference (affine pi b x₀) (affine pi b x₁) =
      difference (affine pi b y₀) (affine pi b y₁) := by
  funext i
  simpa only [difference, affine, xor_cancel_right] using congrFun h (pi i)

def word8 (n : Nat) : Word (Fin 8) :=
  fun i => n.testBit i.val

/-- Concrete bitwise difference data, stated on all eight coordinates.
The proposed proof uses finite kernel reduction, not native evaluation. -/
theorem edge_difference_data :
    (∀ i : Fin 8, difference (word8 1) (word8 3) i = word8 2 i) ∧
    (∀ i : Fin 8, difference (word8 15) (word8 13) i = word8 2 i) ∧
    (∀ i : Fin 8, difference (word8 70) (word8 68) i = word8 2 i) ∧
    (∀ i : Fin 8, difference (word8 85) (word8 21) i = word8 64 i) := by
  decide +kernel

theorem source_parallel :
    difference (word8 1) (word8 3) = difference (word8 15) (word8 13) := by
  exact (funext edge_difference_data.1).trans
    (funext edge_difference_data.2.1).symm

theorem target_not_parallel :
    difference (word8 70) (word8 68) ≠ difference (word8 85) (word8 21) := by
  intro h
  have hwords : word8 2 = word8 64 :=
    (funext edge_difference_data.2.2.1).symm.trans
      (h.trans (funext edge_difference_data.2.2.2))
  have hbit : word8 2 (1 : Fin 8) ≠ word8 64 (1 : Fin 8) := by
    decide +kernel
  exact hbit (congrFun hwords (1 : Fin 8))

/-- The four proposed image equations contradict preservation of parallel
differences. This excludes even nonbijective coordinate-affine maps. -/
theorem no_prescribed_affine (pi : Fin 8 → Fin 8) (b : Word (Fin 8))
    (h₁ : affine pi b (word8 1) = word8 70)
    (h₃ : affine pi b (word8 3) = word8 68)
    (h₁₅ : affine pi b (word8 15) = word8 85)
    (h₁₃ : affine pi b (word8 13) = word8 21) : False := by
  have h := parallel_preserved pi b (word8 1) (word8 3)
    (word8 15) (word8 13) source_parallel
  rw [h₁, h₃, h₁₅, h₁₃] at h
  exact target_not_parallel h

theorem no_affine_assignment :
    ¬ ∃ (pi : Fin 8 → Fin 8) (b : Word (Fin 8)),
      affine pi b (word8 1) = word8 70 ∧
      affine pi b (word8 3) = word8 68 ∧
      affine pi b (word8 15) = word8 85 ∧
      affine pi b (word8 13) = word8 21 := by
  rintro ⟨pi, b, h₁, h₃, h₁₅, h₁₃⟩
  exact no_prescribed_affine pi b h₁ h₃ h₁₅ h₁₃

def source : Array Nat := #[0,1,3,7,15,13,12,28,30,62,46,38,36,52,116,124,108,109,111,103,119,55,183,167,175,173,172,188,184,56,40,41,43,59,187,155,153,137,136,138,202,194,192,193,209,211,243,227,235,233,249,253,245,229,228,230,238,254,250,122,106,98,96,97,113,49,177,161,160,162,178,50,18,82,80,88,72,73,75,91,95,223,207,205,204,220,212,214,150,134,132,133,149,21,85,69,68,70,78]

theorem source_index_data : source.size = 99 ∧
    source[1]! = 1 ∧ source[2]! = 3 ∧ source[4]! = 15 ∧ source[5]! = 13 ∧
    source[97]! = 70 ∧ source[96]! = 68 ∧ source[94]! = 85 ∧ source[93]! = 21 := by
  decide +kernel

theorem source_not_reversed (pi : Fin 8 → Fin 8) (b : Word (Fin 8)) :
    ¬ (∀ i : Fin 99,
      affine pi b (word8 source[i.val]!) = word8 source[98-i.val]!) := by
  intro h
  have h₁ := h (1 : Fin 99)
  have h₃ := h (2 : Fin 99)
  have h₁₅ := h (4 : Fin 99)
  have h₁₃ := h (5 : Fin 99)
  change affine pi b (word8 1) = word8 70 at h₁
  change affine pi b (word8 3) = word8 68 at h₃
  change affine pi b (word8 15) = word8 85 at h₁₅
  change affine pi b (word8 13) = word8 21 at h₁₃
  exact no_prescribed_affine pi b h₁ h₃ h₁₅ h₁₃

#print axioms source_index_data
#print axioms source_not_reversed

#print axioms xor_cancel_right
#print axioms difference_affine
#print axioms parallel_preserved
#print axioms edge_difference_data
#print axioms source_parallel
#print axioms target_not_parallel
#print axioms no_prescribed_affine
#print axioms no_affine_assignment

end ParallelEdges207
