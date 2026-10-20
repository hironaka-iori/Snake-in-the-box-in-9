/-!
# WinCNF: plain CNF semantics (core Lean only)

DIMACS conventions: a literal is a nonzero integer, `v` means variable `v` is true and `-v`
means variable `v` is false.  An assignment is any `τ : Nat → Bool` (variable `0` is unused).
-/
namespace WinCNF

abbrev Lit := Int
abbrev Clause := List Lit
abbrev CNF := List Clause

/-- `litSat τ v = τ v` and `litSat τ (-v) = !τ v`. -/
def litSat (τ : Nat → Bool) : Lit → Bool
  | .ofNat n => τ n
  | .negSucc n => !τ (n + 1)

def clauseSat (τ : Nat → Bool) (c : Clause) : Prop := c.any (litSat τ) = true

def cnfSat (τ : Nat → Bool) (F : CNF) : Prop := ∀ c ∈ F, clauseSat τ c

def unsat (F : CNF) : Prop := ∀ τ : Nat → Bool, (∀ c ∈ F, clauseSat τ c) → False

instance (τ : Nat → Bool) (c : Clause) : Decidable (clauseSat τ c) :=
  inferInstanceAs (Decidable (_ = true))

theorem clauseSat_iff (τ : Nat → Bool) (c : Clause) :
    clauseSat τ c ↔ ∃ l ∈ c, litSat τ l = true := List.any_eq_true

@[simp] theorem litSat_pos (τ : Nat → Bool) (v : Nat) : litSat τ (v : Int) = τ v := rfl
@[simp] theorem litSat_neg (τ : Nat → Bool) (v : Nat) : litSat τ (-((v + 1 : Nat) : Int)) = !τ (v + 1) := rfl

/-- `pos v` is the literal `v`, `neg v` the literal `-v` (for `v ≥ 1`); used in clause data
because they elaborate much faster than `Int` numerals. -/
abbrev pos (v : Nat) : Lit := Int.ofNat v
abbrev neg (v : Nat) : Lit := Int.negSucc (v - 1)

theorem pos_eq (v : Nat) : pos v = (v : Int) := rfl
theorem neg_eq {v : Nat} (h : 1 ≤ v) : neg v = -(v : Int) := by
  cases v with
  | zero => exact absurd h (by decide)
  | succ n => rfl

@[simp] theorem litSat_posv (τ : Nat → Bool) (v : Nat) : litSat τ (pos v) = τ v := rfl
@[simp] theorem litSat_negv (τ : Nat → Bool) {v : Nat} (h : 1 ≤ v) : litSat τ (neg v) = !τ v := by
  cases v with
  | zero => exact absurd h (by decide)
  | succ n => rfl

theorem unsat_of_subset {F G : CNF} (h : ∀ c ∈ F, c ∈ G) (hF : unsat F) : unsat G :=
  fun τ hG => hF τ (fun c hc => hG c (h c hc))

end WinCNF
