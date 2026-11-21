import Prov
/-! Split variant of the cube certificate, for cubes too hard for one certificate.

A cube CNF `f` is split on variables by a binary tree `ST`. Each leaf adds unit clauses (`units ps`)
for the literals on its path. If every leaf CNF `units ps ++ f` is unsatisfiable, so is `f`
(`unsat_of_split`). A leaf certificate uses provenance tags as in `Prov`, plus tag `[]` for
its unit clauses (`coreOkU`, `unsat_of_provU`). -/
namespace Dim8Lift.Split
open Snake9.LocalWindow Dim8Lift.Prov Dim8Lift.Cube

inductive ST where
  | leaf
  | node (v : Nat) (pos neg : ST)

/-- the literal paths of the leaves (positive branch first) -/
def ST.leaves : ST → List (List Int)
  | .leaf => [[]]
  | .node v p n => (p.leaves.map fun ps => (v : Int) :: ps) ++ (n.leaves.map fun ps => (-(v : Int)) :: ps)

def units (ps : List Int) : List (List Int) := ps.map fun l => [l]

theorem cnfTrue_append (τ : Nat → Bool) (a b : List (List Int)) :
    cnfTrue τ (a ++ b) = (cnfTrue τ a && cnfTrue τ b) := by
  simp [cnfTrue, List.all_append]

/-- one literal unit is true under τ when `τ v` agrees with its sign -/
theorem unit_pos (τ : Nat → Bool) (v : Nat) (hv : 0 < v) (h : τ v = true) : cnfTrue τ [[(v : Int)]] = true := by
  have : (0 : Int) < (v : Int) := by omega
  simp [cnfTrue, clauseTrue, litTrue, h, hv]

theorem unit_neg (τ : Nat → Bool) (v : Nat) (hv : 0 < v) (h : τ v = false) : cnfTrue τ [[-(v : Int)]] = true := by
  have : ¬ (0 : Int) < -(v : Int) := by omega
  simp [cnfTrue, clauseTrue, litTrue, h, hv]

/-- all branch variables are positive -/
def ST.pos : ST → Bool
  | .leaf => true
  | .node v p n => decide (0 < v) && p.pos && n.pos

theorem unsat_pre (f : List (List Int)) : ∀ (t : ST) (pre : List Int), t.pos = true →
    (∀ ps ∈ t.leaves, Unsat (units (pre ++ ps) ++ f)) → Unsat (units pre ++ f)
  | .leaf, pre, _, h => by simpa using h [] (by simp [ST.leaves])
  | .node v p n, pre, hp, h => by
    simp only [ST.pos, Bool.and_eq_true, decide_eq_true_eq] at hp
    intro τ
    have hP := unsat_pre f p (pre ++ [(v : Int)]) hp.1.2 (fun ps hps => by
      have := h ((v : Int) :: ps) (by simp [ST.leaves]; exact Or.inl hps)
      simpa using this)
    have hN := unsat_pre f n (pre ++ [-(v : Int)]) hp.2 (fun ps hps => by
      have := h ((-(v : Int)) :: ps) (by simp [ST.leaves]; exact Or.inr hps)
      simpa using this)
    have eP := hP τ; have eN := hN τ
    simp only [units, List.map_append, List.map_cons, List.map_nil, List.append_assoc, cnfTrue_append] at eP eN ⊢
    cases hv : τ v
    · rw [unit_neg τ v hp.1.1 hv] at eN; simpa using eN
    · rw [unit_pos τ v hp.1.1 hv] at eP; simpa using eP

theorem unsat_of_split (f : List (List Int)) (t : ST) (hp : t.pos = true)
    (h : ∀ ps ∈ t.leaves, Unsat (units ps ++ f)) : Unsat f := by
  have := unsat_pre f t [] hp (by simpa using h)
  simpa [units] using this

/-- leaf provenance: tag `[]` marks one of the unit clauses -/
def coreOkU (us : List Int) (c L A k : Nat) (core : List (List Nat × List Nat)) : Bool :=
  core.all fun p => if p.1 = [] then (units us).contains (p.2.map decodeLit)
    else genQ c L A k p.1 == some (p.2.map decodeLit)

theorem coreOkU_append (us : List Int) (c L A k : Nat) (a b : List (List Nat × List Nat)) :
    coreOkU us c L A k (a ++ b) = (coreOkU us c L A k a && coreOkU us c L A k b) := by
  simp [coreOkU, List.all_append]

theorem unsat_of_provU {us : List Int} {c L A k : Nat} (core : List (List Nat × List Nat))
    (h : coreOkU us c L A k core = true) (hU : Unsat (core.map fun p => p.2.map decodeLit)) :
    Unsat (units us ++ cubeCnfQ c L A k) := by
  intro τ
  cases hf : cnfTrue τ (units us ++ cubeCnfQ c L A k)
  · rfl
  · exfalso
    have hc : cnfTrue τ (core.map fun p => p.2.map decodeLit) = true := by
      unfold cnfTrue at *
      rw [List.all_eq_true] at *
      intro cl hcl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcl
      have := List.all_eq_true.mp h p hp
      apply hf
      split at this
      · exact List.mem_append_left _ (List.contains_iff_mem.mp this)
      · simp only [beq_iff_eq] at this; exact List.mem_append_right _ (genQ_mem this)
    rw [hU τ] at hc; exact absurd hc (by simp)

end Dim8Lift.Split
