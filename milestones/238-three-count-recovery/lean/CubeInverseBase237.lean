import Std

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace CubeInverse

/-- An n-bit vertex, with the first bit separated from the remaining bits. -/
def Vertex : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × Vertex n

def flipSum : (n : Nat) → (Vertex n → Int) → Vertex n → Int
  | 0, _, _ => 0
  | n + 1, f, (b, x) =>
    f (!b, x) + flipSum n (fun y => f (b, y)) x

def inner : (n : Nat) → (Vertex n → Int) → (Vertex n → Int) → Int
  | 0, f, g => f () * g ()
  | n + 1, f, g =>
    inner n (fun x => f (false, x)) (fun x => g (false, x)) +
    inner n (fun x => f (true, x)) (fun x => g (true, x))

theorem inner_add_l (n : Nat) (f g h : Vertex n → Int) :
    inner n (fun x => f x + g x) h = inner n f h + inner n g h := by
  induction n with
  | zero => exact Int.add_mul _ _ _
  | succ n ih => simp only [inner, ih]; omega

theorem inner_add_r (n : Nat) (f g h : Vertex n → Int) :
    inner n f (fun x => g x + h x) = inner n f g + inner n f h := by
  induction n with
  | zero => exact Int.mul_add _ _ _
  | succ n ih => simp only [inner, ih]; omega

theorem self_adjoint (n : Nat) (f g : Vertex n → Int) :
    inner n f (flipSum n g) = inner n (flipSum n f) g := by
  induction n with
  | zero => simp [inner, flipSum]
  | succ n ih =>
    simp only [inner, flipSum, Bool.not_false, Bool.not_true, inner_add_l,
      inner_add_r, ih]
    omega

def translate : (n : Nat) → Vertex n → Vertex n → Vertex n
  | 0, _, _ => ()
  | n + 1, (b, x), (c, y) =>
    (if b then !c else c, translate n x y)

theorem flip_translate (n : Nat) (f : Vertex n → Int) (a x : Vertex n) :
    flipSum n (fun y => f (translate n a y)) x = flipSum n f (translate n a x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    rcases x with ⟨c, x⟩
    cases b <;> cases c <;> simp [translate, flipSum]
    · exact ih (fun y => f (false, y)) a x
    · exact ih (fun y => f (true, y)) a x
    · exact ih (fun y => f (true, y)) a x
    · exact ih (fun y => f (false, y)) a x

def weight : (n : Nat) → Vertex n → Nat
  | 0, _ => 0
  | n + 1, (b, x) => (if b then 1 else 0) + weight n x

def coefficient : Nat → Int
  | 1 => 35
  | 3 => -10
  | 5 => 8
  | 7 => -16
  | 9 => 128
  | _ => 0

def spike : (n : Nat) → Vertex n → Int
  | 0, _ => 315
  | n + 1, (b, x) => if b then 0 else spike n x

theorem inner_zero_l (n : Nat) (f : Vertex n → Int) :
    inner n (fun _ => 0) f = 0 := by
  induction n with
  | zero => simp [inner]
  | succ n ih => simp [inner, ih]

theorem inner_spike (n : Nat) (a : Vertex n) (f : Vertex n → Int) :
    inner n (fun x => spike n (translate n a x)) f = 315 * f a := by
  induction n with
  | zero => cases a; rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    cases b <;> simp [inner, translate, spike, ih, inner_zero_l]

def every : (n : Nat) → (Vertex n → Bool) → Bool
  | 0, f => f ()
  | n + 1, f =>
    every n (fun x => f (false, x)) && every n (fun x => f (true, x))

theorem of_every (n : Nat) (p : Vertex n → Bool) (h : every n p = true)
    (x : Vertex n) : p x = true := by
  induction n with
  | zero => cases x; exact h
  | succ n ih =>
    rcases x with ⟨b, x⟩
    obtain ⟨l, r⟩ := Bool.and_eq_true_iff.mp h
    cases b
    · exact ih _ l x
    · exact ih _ r x


#print axioms self_adjoint
#print axioms inner_spike
#print axioms of_every

end CubeInverse
