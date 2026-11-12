import LayerJoining

namespace QuotientLift195
open LayerJoining

/-- Lift a path from a quotient when every consecutive edge has been lifted. -/
def liftPath {V B : Type} {R : V → V → Prop} {S : B → B → Prop}
    {m : Nat} (q : InducedPath B S m) (projection : V → B)
    (p : Fin (m+1) → V)
    (agreement : ∀ i, projection (p i) = q.vertex i)
    (projects : ∀ x y, R x y → S (projection x) (projection y))
    (steps : ∀ i j, i.val+1=j.val → R (p i) (p j)) :
    InducedPath V R m where
  vertex := p
  distinct i j eq := by
    apply q.distinct i j
    rw [← agreement i, ← agreement j]
    exact congrArg projection eq
  induced i j order := by
    constructor
    · intro edge
      have base := projects (p i) (p j) edge
      rw [agreement i, agreement j] at base
      exact (q.induced i j order).mp base
    · exact steps i j

/-- The two lifts cannot intersect or have an edge between them. -/
theorem separateLifts {V B : Type} {R : V → V → Prop} {S : B → B → Prop}
    {m : Nat} (q : InducedPath B S m) (projection : V → B)
    (p : Fin (m+1) → V) (g : V → V)
    (agreement : ∀ i, projection (p i) = q.vertex i)
    (sameFibre : ∀ x, projection (g x) = projection x)
    (noFixed : ∀ x, x ≠ g x)
    (noFibreEdge : ∀ x, ¬ R x (g x))
    (symmetric : ∀ x y, R x y → R y x)
    (involution : ∀ x, g (g x) = x)
    (automorphism : ∀ x y, R x y → R (g x) (g y))
    (projects : ∀ x y, R x y → S (projection x) (projection y))
    (uniqueEdge : ∀ x y, R x y → ¬ R x (g y))
    (steps : ∀ i j, i.val+1=j.val → R (p i) (p j)) :
    ∀ i j, p i ≠ g (p j) ∧ ¬ R (p i) (g (p j)) := by
  intro i j
  constructor
  · intro eq
    have index : i=j := by
      apply q.distinct i j
      have he := congrArg projection eq
      rw [sameFibre, agreement i, agreement j] at he
      exact he
    subst j
    exact noFixed (p i) eq
  · intro edge
    by_cases eq : i=j
    · subst j; exact noFibreEdge (p i) edge
    · by_cases order : i.val<j.val
      · have base := projects (p i) (g (p j)) edge
        rw [sameFibre, agreement i, agreement j] at base
        have consecutive := (q.induced i j order).mp base
        exact uniqueEdge (p i) (p j) (steps i j consecutive) edge
      · have order' : j.val<i.val := by
          have ne : i.val≠j.val := by intro he; exact eq (Fin.ext he)
          omega
        have reverse : R (p j) (g (p i)) := by
          have h := automorphism _ _ (symmetric _ _ edge)
          simpa only [involution] using h
        have base := projects (p j) (g (p i)) reverse
        rw [sameFibre, agreement j, agreement i] at base
        have consecutive := (q.induced j i order').mp base
        exact uniqueEdge (p j) (p i) (steps j i consecutive) reverse

/-- An automorphism sends an induced path to an induced path. -/
def partnerPath {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m) (g : V → V)
    (involution : ∀ x, g (g x)=x)
    (automorphism : ∀ x y, R (g x) (g y) ↔ R x y) :
    InducedPath V R m where
  vertex i := g (p.vertex i)
  distinct i j eq := by
    apply p.distinct i j
    have h := congrArg g eq
    simpa only [involution] using h
  induced i j order := by
    rw [automorphism]
    exact p.induced i j order

#print axioms liftPath
#print axioms separateLifts
#print axioms partnerPath
end QuotientLift195
