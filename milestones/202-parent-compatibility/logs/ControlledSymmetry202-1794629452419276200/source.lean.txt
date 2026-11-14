import LayerJoining

namespace ControlledSymmetry202
open LayerJoining

def squareAdj (u v : Bool × Bool) : Prop :=
  (u.1 ≠ v.1 ∧ u.2=v.2) ∨ (u.1=v.1 ∧ u.2 ≠ v.2)

def active (epsilon : Bool) (u : Bool × Bool) : Prop :=
  Bool.xor u.1 u.2 = epsilon

instance (u v : Bool × Bool) : Decidable (squareAdj u v) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

instance (epsilon : Bool) (u : Bool × Bool) : Decidable (active epsilon u) :=
  inferInstanceAs (Decidable (Bool.xor u.1 u.2 = epsilon))

def reflect (epsilon : Bool) (u : Bool × Bool) : Bool × Bool :=
  if epsilon then (u.2,u.1) else (!u.2,!u.1)

def twist (epsilon control : Bool) (u : Bool × Bool) : Bool × Bool :=
  if control then reflect epsilon u else u

def Adj {V : Type} (R : V → V → Prop) (x y : V × (Bool × Bool)) : Prop :=
  (x.1=y.1 ∧ squareAdj x.2 y.2) ∨ (R x.1 y.1 ∧ x.2=y.2)

def change {V : Type} (epsilon : Bool) (f : V → Bool)
    (x : V × (Bool × Bool)) : V × (Bool × Bool) :=
  (x.1,twist epsilon (f x.1) x.2)

theorem fibreInvolution : ∀ epsilon c a b : Bool,
    twist epsilon c (twist epsilon c (a,b))=(a,b) := by decide +kernel

theorem fibreActive : ∀ epsilon c a b : Bool,
    active epsilon (twist epsilon c (a,b)) ↔ active epsilon (a,b) := by decide +kernel

theorem fibreAdjacency : ∀ epsilon c a b d e : Bool,
    squareAdj (twist epsilon c (a,b)) (twist epsilon c (d,e)) ↔
      squareAdj (a,b) (d,e) := by decide +kernel

theorem matchingCriterion : ∀ epsilon c d a b e f : Bool,
    ((twist epsilon c (a,b)=twist epsilon d (e,f)) ↔ (a,b)=(e,f)) ↔
    (c=d ∨ ¬ (active epsilon (a,b) ∧ active epsilon (e,f))) := by decide +kernel

theorem composition : ∀ epsilon c d a b : Bool,
    twist epsilon c (twist epsilon d (a,b))=
      twist epsilon (Bool.xor c d) (a,b) := by decide +kernel

theorem involution {V : Type} (epsilon : Bool) (f : V → Bool)
    (x : V × (Bool × Bool)) : change epsilon f (change epsilon f x)=x := by
  rcases x with ⟨z,a,b⟩
  exact congrArg (fun u => (z,u)) (fibreInvolution epsilon (f z) a b)

theorem injective {V : Type} (epsilon : Bool) (f : V → Bool)
    (x y : V × (Bool × Bool)) (h : change epsilon f x=change epsilon f y) : x=y := by
  have h' := congrArg (change epsilon f) h
  simpa only [involution] using h'

theorem pairCriterion {V : Type} (R : V → V → Prop) (epsilon : Bool) (f : V → Bool)
    (x y : V × (Bool × Bool)) :
    (Adj R (change epsilon f x) (change epsilon f y) ↔ Adj R x y) ↔
    (R x.1 y.1 → active epsilon x.2 → active epsilon y.2 → f x.1=f y.1) := by
  classical
  rcases x with ⟨z,a,b⟩
  rcases y with ⟨w,c,d⟩
  by_cases eq : z=w
  · subst w
    have ha := fibreAdjacency epsilon (f z) a b c d
    have he : twist epsilon (f z) (a,b)=twist epsilon (f z) (c,d) ↔ (a,b)=(c,d) := by
      constructor
      · intro h
        have h' := congrArg (twist epsilon (f z)) h
        simpa only [fibreInvolution] using h'
      · intro h; rw [h]
    simpa only [Adj,change,Prod.fst,Prod.snd,ha,he,true_and,implies_true,iff_self]
  · by_cases hr : R z w
    · have h := matchingCriterion epsilon (f z) (f w) a b c d
      simp only [Adj,change,Prod.fst,Prod.snd,eq,false_and,false_or,hr,true_and, true_implies]
      rw [h]
      constructor
      · intro h ha hb
        rcases h with h | h
        · exact h
        · exact False.elim (h ⟨ha,hb⟩)
      · intro h
        by_cases ha : active epsilon (a,b)
        · by_cases hb : active epsilon (c,d)
          · exact Or.inl (h ha hb)
          · exact Or.inr (fun h => hb h.2)
        · exact Or.inr (fun h => ha h.1)
    · simp [Adj,change,eq,hr]

theorem wholeSetCriterion {V : Type} (R : V → V → Prop) (epsilon : Bool)
    (f : V → Bool) (S : V × (Bool × Bool) → Prop) :
    (∀ x y, S x → S y → (Adj R (change epsilon f x) (change epsilon f y) ↔ Adj R x y)) ↔
    (∀ x y, S x → S y → R x.1 y.1 → active epsilon x.2 → active epsilon y.2 → f x.1=f y.1) := by
  constructor
  · intro h x y hx hy
    exact (pairCriterion R epsilon f x y).mp (h x y hx hy)
  · intro h x y hx hy
    exact (pairCriterion R epsilon f x y).mpr (h x y hx hy)

def imagePath {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath (V × (Bool × Bool)) (Adj R) m) (epsilon : Bool) (f : V → Bool)
    (compatible : ∀ i j, R (p.vertex i).1 (p.vertex j).1 →
      active epsilon (p.vertex i).2 → active epsilon (p.vertex j).2 →
      f (p.vertex i).1=f (p.vertex j).1) :
    InducedPath (V × (Bool × Bool)) (Adj R) m where
  vertex i := change epsilon f (p.vertex i)
  distinct i j eq := p.distinct i j (injective epsilon f _ _ eq)
  induced i j hij := ((pairCriterion R epsilon f _ _).mpr (compatible i j)).trans (p.induced i j hij)

#print axioms fibreInvolution
#print axioms fibreActive
#print axioms fibreAdjacency
#print axioms matchingCriterion
#print axioms composition
#print axioms involution
#print axioms injective
#print axioms pairCriterion
#print axioms wholeSetCriterion
#print axioms imagePath
end ControlledSymmetry202
