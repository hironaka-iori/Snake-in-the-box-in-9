import Std

namespace CubeSyndrome

def add (a b : Bool) : Bool := xor a b

theorem paired (a b c : Bool) : add (add a b) (add b c) = add a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem commuteFour (a b c d : Bool) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The two slices give the parity of selected neighbours in one more dimension. -/
def lift {V : Type} (D : (V → Bool) → V → Bool)
    (s : Bool → V → Bool) (layer : Bool) (x : V) : Bool :=
  add (D (s layer) x) (s (!layer) x)

theorem liftLinear {V : Type} (D : (V → Bool) → V → Bool)
    (linear : ∀ a b x, D (fun y => add (a y) (b y)) x = add (D a x) (D b x))
    (a b : Bool → V → Bool) (layer : Bool) (x : V) :
    lift D (fun l y => add (a l y) (b l y)) layer x =
      add (lift D a layer x) (lift D b layer x) := by
  unfold lift
  rw [linear]
  apply commuteFour

theorem liftSquare {V : Type} (D : (V → Bool) → V → Bool)
    (linear : ∀ a b x, D (fun y => add (a y) (b y)) x = add (D a x) (D b x))
    (s : Bool → V → Bool) (layer : Bool) (x : V) :
    lift D (lift D s) layer x = add (D (D (s layer)) x) (s layer x) := by
  unfold lift
  rw [linear]
  cases layer <;> apply paired

def Cube : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Cube n

def D : (n : Nat) → (Cube n → Bool) → Cube n → Bool
  | 0, _, _ => false
  | n+1, f, (l,x) => lift (D n) (fun t y => f (t,y)) l x

theorem linear (n : Nat) (s t : Cube n → Bool) (x : Cube n) :
    D n (fun y => add (s y) (t y)) x = add (D n s x) (D n t x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨l,x⟩ := x
    exact liftLinear (D n) ih (fun l y => s (l,y)) (fun l y => t (l,y)) l x

def odd : Nat → Bool
  | 0 => false
  | n+1 => !(odd n)

theorem square (n : Nat) (s : Cube n → Bool) (x : Cube n) :
    D n (D n s) x = if odd n then s x else false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨l,x⟩ := x
    change lift (D n) (lift (D n) (fun t y => s (t,y))) l x = _
    rw [liftSquare (D n) (linear n), ih]
    change add (if odd n then s (l,x) else false) (s (l,x)) =
      (if !(odd n) then s (l,x) else false)
    cases odd n <;> cases s (l,x) <;> rfl

theorem invertNine (s : Cube 9 → Bool) (x : Cube 9) :
    D 9 (D 9 s) x = s x := square 9 s x

#print axioms linear
#print axioms square
#print axioms invertNine
end CubeSyndrome
