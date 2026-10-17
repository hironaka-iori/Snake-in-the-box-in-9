import CubeLocal
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Fintype

namespace Snake9.Window244
noncomputable section
set_option maxHeartbeats 800000

/-- Any two injections of the same finite index type into the coordinates
extend to a coordinate permutation. -/
theorem permutation_extends {n : Nat} (f g : Fin n → Coord)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : Equiv.Perm Coord, ∀ i, σ (f i) = g i := by
  let ef := Equiv.ofInjective f hf
  let eg := Equiv.ofInjective g hg
  let e := ef.symm.trans eg
  refine ⟨e.extendSubtype,?_⟩
  intro i
  rw [Equiv.extendSubtype_apply_of_mem e (f i) ⟨i,rfl⟩]
  change g (ef.symm (ef i)) = g i
  rw [ef.symm_apply_apply]

theorem coordinate_permutation_three (c a b : Coord)
    (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm Coord, σ c = 0 ∧ σ a = 1 ∧ σ b = 2 := by
  let f : Fin 3 → Coord := ![c,a,b]
  let g : Fin 3 → Coord := fun i => ⟨i.val,by omega⟩
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hg : Function.Injective g := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Coord => x.val) h
  obtain ⟨σ,hσ⟩ := permutation_extends f g hf hg
  refine ⟨σ,?_,?_,?_⟩
  · simpa [f,g] using hσ 0
  · simpa [f,g] using hσ 1
  · simpa [f,g] using hσ 2

theorem coordinate_permutation_four (c a b d : Coord)
    (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm Coord, σ c = 0 ∧ σ a = 1 ∧ σ b = 2 ∧ σ d = 3 := by
  let f : Fin 4 → Coord := ![c,a,b,d]
  let g : Fin 4 → Coord := fun i => ⟨i.val,by omega⟩
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hg : Function.Injective g := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Coord => x.val) h
  obtain ⟨σ,hσ⟩ := permutation_extends f g hf hg
  refine ⟨σ,?_,?_,?_,?_⟩
  · simpa [f,g] using hσ 0
  · simpa [f,g] using hσ 1
  · simpa [f,g] using hσ 2
  · simpa [f,g] using hσ 3

#print axioms permutation_extends
#print axioms coordinate_permutation_three
#print axioms coordinate_permutation_four
end
end Snake9.Window244
