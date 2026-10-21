import LocalWindowModel

/-! Renaming variables preserves an unsatisfiable Boolean formula. The direction
used here maps a compact proof's variables back to the original DIMACS ids.
Injectivity is not needed in this direction. -/
namespace Snake9.LocalWindow

def renameLit (f : Nat → Nat) (l : Int) : Int :=
  if 0 < l then Int.ofNat (f l.toNat) else -Int.ofNat (f (-l).toNat)

def renameCnf (f : Nat → Nat) (cnf : List (List Int)) : List (List Int) :=
  cnf.map fun cl => cl.map (renameLit f)

theorem litTrue_rename (f : Nat → Nat) (hf : ∀ n, 0 < f n)
    (τ : Nat → Bool) (l : Int) :
    litTrue τ (renameLit f l) = litTrue (fun n => τ (f n)) l := by
  unfold renameLit litTrue
  by_cases h : 0 < l
  · simp [h, hf]
  · have hn : ¬ ((f (-l).toNat : Nat) : Int) < 0 :=
      Int.not_lt.mpr (Int.ofNat_nonneg _)
    simp [h, hf, hn]

theorem cnfTrue_rename (f : Nat → Nat) (hf : ∀ n, 0 < f n)
    (τ : Nat → Bool) (cnf : List (List Int)) :
    cnfTrue τ (renameCnf f cnf) = cnfTrue (fun n => τ (f n)) cnf := by
  simp only [cnfTrue, renameCnf, List.all_map, clauseTrue, List.any_map,
    Function.comp_def, litTrue_rename f hf]
  rfl

theorem Unsat.rename {cnf : List (List Int)} (h : Unsat cnf)
    (f : Nat → Nat) (hf : ∀ n, 0 < f n) : Unsat (renameCnf f cnf) := by
  intro τ
  rw [cnfTrue_rename f hf]
  exact h (fun n => τ (f n))

#print axioms Unsat.rename
end Snake9.LocalWindow
