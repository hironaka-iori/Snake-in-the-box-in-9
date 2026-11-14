import Std
import CubeSyndrome

namespace CubeSyndrome

def weight : (d : Nat) → (Cube d → Bool) → Nat
  | 0, f => if f () then 1 else 0
  | n+1, f => weight n (fun x => f (false,x)) + weight n (fun x => f (true,x))

def both (d : Nat) (f g : Cube d → Bool) : Nat :=
  weight d (fun x => f x && g x)

theorem weightAdd (d : Nat) (f g : Cube d → Bool) :
    weight d (fun x => add (f x) (g x)) + 2 * both d f g = weight d f + weight d g := by
  induction d with
  | zero =>
    cases h : f () <;> cases k : g () <;> simp [weight, both, add, h, k]
  | succ n ih =>
    have h₀ := ih (fun x => f (false,x)) (fun x => g (false,x))
    have h₁ := ih (fun x => f (true,x)) (fun x => g (true,x))
    simp only [both, weight] at h₀ h₁ ⊢
    omega

theorem bothComm (d : Nat) (f g : Cube d → Bool) : both d f g = both d g f := by
  simp only [both, Bool.and_comm]

theorem distributeAdd (p q r : Bool) : (add p q && r) = add (p && r) (q && r) := by
  cases p <;> cases q <;> cases r <;> decide

theorem bothAddParity (d : Nat) (f g h : Cube d → Bool) :
    both d (fun x => add (f x) (g x)) h % 2 =
      (both d f h + both d g h) % 2 := by
  have eq := weightAdd d (fun x => f x && h x) (fun x => g x && h x)
  simp only [both, distributeAdd] at eq ⊢
  omega

theorem adjointParity (d : Nat) (f g : Cube d → Bool) :
    both d (D d f) g % 2 = both d (D d g) f % 2 := by
  induction d with
  | zero => simp [both, weight, D]
  | succ n ih =>
    let f₀ := fun x => f (false,x)
    let f₁ := fun x => f (true,x)
    let g₀ := fun x => g (false,x)
    let g₁ := fun x => g (true,x)
    have e₀ := ih f₀ g₀
    have e₁ := ih f₁ g₁
    have a₀ := bothAddParity n (D n f₀) f₁ g₀
    have a₁ := bothAddParity n (D n f₁) f₀ g₁
    have b₀ := bothAddParity n (D n g₀) g₁ f₀
    have b₁ := bothAddParity n (D n g₁) g₀ f₁
    have c₀ := bothComm n f₁ g₀
    have c₁ := bothComm n f₀ g₁
    change (both n (fun x => add (D n f₀ x) (f₁ x)) g₀ +
            both n (fun x => add (D n f₁ x) (f₀ x)) g₁) % 2 =
           (both n (fun x => add (D n g₀ x) (g₁ x)) f₀ +
            both n (fun x => add (D n g₁ x) (g₀ x)) f₁) % 2
    omega

theorem weightOddNeighbours (d : Nat) (f : Cube d → Bool) :
    weight d (D d f) % 4 = (d * weight d f) % 4 := by
  induction d with
  | zero => simp [weight, D]
  | succ n ih =>
    let a := fun x => f (false,x)
    let b := fun x => f (true,x)
    have w₀ := ih a
    have w₁ := ih b
    have e₀ := weightAdd n (D n a) b
    have e₁ := weightAdd n (D n b) a
    have cross := adjointParity n a b
    change (weight n (fun x => add (D n a x) (b x)) +
            weight n (fun x => add (D n b x) (a x))) % 4 =
           ((n+1) * (weight n a + weight n b)) % 4
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
    omega

#print axioms adjointParity
#print axioms weightOddNeighbours

end CubeSyndrome
