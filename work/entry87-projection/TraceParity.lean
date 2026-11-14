import Clique

namespace Entry87.Parity

/-- A coordinate changes precisely when the base side does not consume the step.
The recurrence works for every length and does not enumerate the free cube. -/
theorem assigned (labelChanges : Nat → Bool) (freeParity : Nat → Bool)
    (id : Nat → Nat) (initial : id 0 = 0)
    (ids : ∀ i, id (i+1) = id i + (if labelChanges i then 0 else 1))
    (stay : ∀ i, labelChanges i = true → freeParity (i+1) = freeParity i)
    (flip : ∀ i, labelChanges i = false → freeParity (i+1) = !freeParity i) :
    ∀ i, freeParity i = (if id i % 2 = 0 then freeParity 0 else !freeParity 0) := by
  intro i
  induction i with
  | zero => simp [initial]
  | succ i ih =>
    cases eq : labelChanges i with
    | true =>
      rw [stay i eq, ih, ids i]
      simp [eq]
    | false =>
      rw [flip i eq, ih, ids i]
      simp only [eq, Bool.false_eq_true, ↓reduceIte]
      by_cases h : id i % 2 = 0
      · have h' : (id i + 1) % 2 ≠ 0 := by omega
        simp [h,h']
      · have h' : (id i + 1) % 2 = 0 := by omega
        simp [h,h']

/-- Pairwise incompatibility itself implies a sharp lower bound on total used
colors, and hence limits the number of missing words in the finite supply. -/
theorem missingBudget {W I : Type} [DecidableEq W] (family : List I)
    (word : I → W) (conflict : I → I → Prop)
    (clique : family.Pairwise conflict)
    (apart : ∀ i j, conflict i j → word i ≠ word j)
    (used missing palette : List W)
    (inside : ∀ i ∈ family, word i ∈ used)
    (decompose : used.length + missing.length = palette.length) :
    family.length + missing.length ≤ palette.length := by
  have bound := Entry87.cliqueCapacity family conflict word used clique apart inside
  omega

#print axioms assigned
#print axioms missingBudget
end Entry87.Parity
