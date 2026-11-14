import Std

set_option Elab.async false

namespace Joint216

/-- Restricting all three pair relations to pairs occurring in a fitting
triple preserves every complete assignment satisfying the original relations. -/
theorem pair_projection_preserves
    (A B C : List Nat) (R S T : Nat → Nat → Bool)
    (a b c : Nat) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (hR : R a b = true) (hS : S b c = true) (hT : T a c = true) :
    (R a b && C.any (fun z => S b z && T a z)) = true ∧
    (S b c && A.any (fun x => R x b && T x c)) = true ∧
    (T a c && B.any (fun y => R a y && S y c)) = true := by
  constructor
  · rw [hR]
    simp only [Bool.true_and]
    exact List.any_eq_true.mpr ⟨c, hc, by simp [hS, hT]⟩
  · constructor
    · rw [hS]
      simp only [Bool.true_and]
      exact List.any_eq_true.mpr ⟨a, ha, by simp [hR, hT]⟩
    · rw [hT]
      simp only [Bool.true_and]
      exact List.any_eq_true.mpr ⟨b, hb, by simp [hR, hS]⟩

/-- Root-domain projections stay sound in every subdomain. -/
theorem projection_preserves_subdomain_assignment
    (A B C A' B' C' : List Nat) (R S T : Nat → Nat → Bool)
    (hA : ∀ x, x ∈ A' → x ∈ A)
    (hB : ∀ x, x ∈ B' → x ∈ B)
    (hC : ∀ x, x ∈ C' → x ∈ C)
    (a b c : Nat) (ha : a ∈ A') (hb : b ∈ B') (hc : c ∈ C')
    (hR : R a b = true) (hS : S b c = true) (hT : T a c = true) :
    (R a b && C.any (fun z => S b z && T a z)) = true ∧
    (S b c && A.any (fun x => R x b && T x c)) = true ∧
    (T a c && B.any (fun y => R a y && S y c)) = true := by
  exact pair_projection_preserves A B C R S T a b c
    (hA a ha) (hB b hb) (hC c hc) hR hS hT

/-- No supported triple means no fitting complete assignment. -/
theorem empty_joint_support_impossible
    (A B C : List Nat) (R S T : Nat → Nat → Bool)
    (a b c : Nat) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (hR : R a b = true) (hS : S b c = true) (hT : T a c = true)
    (hempty : A.any (fun x => B.any (fun y => R x y &&
      C.any (fun z => S y z && T x z))) = false) : False := by
  have h := (pair_projection_preserves A B C R S T a b c ha hb hc hR hS hT).1
  have hb' : B.any (fun y => R a y && C.any (fun z => S y z && T a z)) = true :=
    List.any_eq_true.mpr ⟨b, hb, h⟩
  have ha' : A.any (fun x => B.any (fun y => R x y &&
      C.any (fun z => S y z && T x z))) = true :=
    List.any_eq_true.mpr ⟨a, ha, hb'⟩
  rw [hempty] at ha'
  contradiction

#print axioms pair_projection_preserves
#print axioms projection_preserves_subdomain_assignment
#print axioms empty_joint_support_impossible
end Joint216
