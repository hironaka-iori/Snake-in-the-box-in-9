import LayerJoining

namespace IsometricPlacement199
open LayerJoining

def imagePath {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m) (f : V → V)
    (inj : ∀ x y, f x = f y → x = y)
    (adj : ∀ x y, R (f x) (f y) ↔ R x y) : InducedPath V R m where
  vertex i := f (p.vertex i)
  distinct i j eq := p.distinct i j (inj _ _ eq)
  induced i j hij := (adj _ _).trans (p.induced i j hij)

def inLayer {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m) (b : Bool) :
    InducedPath (V × Bool) (LayerAdj R) m where
  vertex i := (p.vertex i,b)
  distinct i j eq := p.distinct i j (congrArg Prod.fst eq)
  induced i j hij := by simpa [LayerAdj] using p.induced i j hij

theorem separated_iff {V : Type} {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b) (f : V → V) :
    (∀ i j, ¬ LayerAdj R (p.vertex i,false) (f (q.vertex j),true)) ↔
    (∀ i j, p.vertex i ≠ f (q.vertex j)) := by
  simp only [LayerAdj, Bool.false_eq_true, false_and, ne_eq,
    not_false_eq_true, true_and, false_or]

theorem change_representatives {V : Type} (S T : V → Prop)
    (f phi psi invPsi : V → V)
    (inj : ∀ x y, phi x = phi y → x = y)
    (leftInverse : ∀ x, invPsi (psi x) = x) :
    (∀ x y, S x → T y → x ≠ f y) ↔
    (∀ x y, S x → T y → phi x ≠ phi (f (invPsi (psi y)))) := by
  constructor
  · intro h x y hx hy eq
    apply h x y hx hy
    apply inj
    simpa only [leftInverse] using eq
  · intro h x y hx hy eq
    apply h x y hx hy
    simpa only [leftInverse,eq]

theorem reverse_pair {V : Type} (S T : V → Prop) (f g : V → V)
    (leftInverse : ∀ x, g (f x) = x)
    (rightInverse : ∀ x, f (g x) = x) :
    (∀ x y, S x → T y → x ≠ f y) ↔
    (∀ y x, T y → S x → y ≠ g x) := by
  constructor
  · intro h y x hy hx eq
    apply h x y hx hy
    rw [eq,rightInverse]
  · intro h x y hx hy eq
    apply h y x hy hx
    rw [eq,leftInverse]

#print axioms imagePath
#print axioms inLayer
#print axioms separated_iff
#print axioms change_representatives
#print axioms reverse_pair
end IsometricPlacement199
