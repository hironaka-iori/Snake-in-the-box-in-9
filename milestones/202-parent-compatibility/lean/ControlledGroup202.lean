import ControlledSymmetry202

namespace ControlledGroup202
open ControlledSymmetry202

theorem twistDetermined : ∀ epsilon c d a b : Bool,
    (active epsilon (a,b) → c=d) → twist epsilon c (a,b)=twist epsilon d (a,b) := by
  decide +kernel

theorem compose {V : Type} (epsilon : Bool) (f g : V → Bool)
    (x : V × (Bool × Bool)) :
    change epsilon f (change epsilon g x)=change epsilon (fun z => Bool.xor (f z) (g z)) x := by
  rcases x with ⟨z,a,b⟩
  exact congrArg (fun u => (z,u)) (composition epsilon (f z) (g z) a b)

theorem complement {V : Type} (epsilon : Bool) (f : V → Bool)
    (x : V × (Bool × Bool)) :
    change epsilon (fun z => !(f z)) x=change epsilon (fun _ => true) (change epsilon f x) := by
  rw [compose]
  have h : (fun z => !(f z))=(fun z => Bool.xor true (f z)) := by
    funext z; cases f z <;> rfl
  rw [h]

theorem globalReflection {V : Type} (R : V → V → Prop) (epsilon : Bool)
    (x y : V × (Bool × Bool)) :
    Adj R (change epsilon (fun _ => true) x) (change epsilon (fun _ => true) y) ↔ Adj R x y := by
  exact (pairCriterion R epsilon (fun _ => true) x y).mpr (by intros; rfl)

theorem rigidOnSet {V : Type} (epsilon c : Bool) (f : V → Bool)
    (S : V × (Bool × Bool) → Prop)
    (constant : ∀ x, S x → active epsilon x.2 → f x.1=c) :
    ∀ x, S x → change epsilon f x=change epsilon (fun _ => c) x := by
  intro x hx
  rcases x with ⟨z,a,b⟩
  exact congrArg (fun u => (z,u)) (twistDetermined epsilon (f z) c a b (constant (z,a,b) hx))

theorem compatibilityStable {V : Type} (R : V → V → Prop) (epsilon : Bool)
    (f g : V → Bool) (S : V × (Bool × Bool) → Prop)
    (h : ∀ x y, S x → S y → R x.1 y.1 → active epsilon x.2 → active epsilon y.2 → g x.1=g y.1) :
    ∀ x y, S x → S y → R (change epsilon f x).1 (change epsilon f y).1 →
      active epsilon (change epsilon f x).2 → active epsilon (change epsilon f y).2 →
      g (change epsilon f x).1=g (change epsilon f y).1 := by
  intro x y hx hy hr ha hb
  rcases x with ⟨z,a,b⟩
  rcases y with ⟨w,c,d⟩
  exact h (z,a,b) (w,c,d) hx hy hr
    ((fibreActive epsilon (f z) a b).mp ha) ((fibreActive epsilon (f w) c d).mp hb)

theorem xorCompatible {V : Type} (R : V → V → Prop) (epsilon : Bool)
    (f g : V → Bool) (S : V × (Bool × Bool) → Prop)
    (hf : ∀ x y, S x → S y → R x.1 y.1 → active epsilon x.2 → active epsilon y.2 → f x.1=f y.1)
    (hg : ∀ x y, S x → S y → R x.1 y.1 → active epsilon x.2 → active epsilon y.2 → g x.1=g y.1) :
    ∀ x y, S x → S y → R x.1 y.1 → active epsilon x.2 → active epsilon y.2 →
      Bool.xor (f x.1) (g x.1)=Bool.xor (f y.1) (g y.1) := by
  intro x y hx hy hr ha hb
  rw [hf x y hx hy hr ha hb,hg x y hx hy hr ha hb]

theorem threeComponents (selected unselected : Nat) (h : selected+unselected ≤ 3) :
    selected ≤ 1 ∨ unselected ≤ 1 := by omega

#print axioms twistDetermined
#print axioms compose
#print axioms complement
#print axioms globalReflection
#print axioms rigidOnSet
#print axioms compatibilityStable
#print axioms xorCompatible
#print axioms threeComponents
end ControlledGroup202
