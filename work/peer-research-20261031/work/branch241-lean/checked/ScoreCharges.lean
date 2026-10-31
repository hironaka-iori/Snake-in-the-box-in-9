import Std
import Lean.Elab.Tactic.Omega

/-!
Exact integer formalization of the adaptive charge inequality.
Geometry is exposed as two explicit counting premises (D=3e3, V=sum occupancy).
The resulting theorem is NOT a complete geometric bridge for actual snakes.
-/
namespace Q9Charge
structure Fibre where
  h : Fin 7
  t : Fin 3

def deficit (f : Fibre) : Nat := 7 - (f.h.val + 1)
def support (f : Fibre) : Nat := 13 - (f.h.val + 1)
def bonus (f : Fibre) : Nat :=
  (if f.t.val + 1 ≤ 2 then 1 else 0) +
    3 * (if f.t.val + 1 = 1 then 1 else 0)
def share (f : Fibre) : Nat := 2520 / ((f.h.val + 1) * (f.t.val + 1))

def total (f : Fibre → Nat) : List Fibre → Nat
  | [] => 0
  | a :: xs => f a + total f xs

/-- Every scaled adaptive share is an EXACT integer, not a floor approximation. -/
theorem share_exact : ∀ h : Fin 7, ∀ t : Fin 3,
    (2520 / ((h.val + 1) * (t.val + 1))) *
      ((h.val + 1) * (t.val + 1)) = 2520 := by
  decide +kernel

theorem share_lower_table : ∀ h : Fin 7, ∀ t : Fin 3,
    20 * (13 - (h.val + 1)) +
      60 * ((if t.val + 1 ≤ 2 then 1 else 0) +
        3 * (if t.val + 1 = 1 then 1 else 0)) ≤
    2520 / ((h.val + 1) * (t.val + 1)) := by
  decide +kernel

theorem share_lower (f : Fibre) :
    20 * support f + 60 * bonus f ≤ share f := by
  exact share_lower_table f.h f.t

theorem support_identity (xs : List Fibre) :
    total support xs = 6 * xs.length + total deficit xs := by
  induction xs with
  | nil => simp [total]
  | cons f xs ih =>
    have hi : support f = 6 + deficit f := by
      have hf := f.h.isLt
      unfold support deficit
      omega
    simp only [total, List.length_cons]
    omega

theorem total_lower (xs : List Fibre) :
    20 * total support xs + 60 * total bonus xs ≤ total share xs := by
  induction xs with
  | nil => simp [total]
  | cons f xs ih =>
    have hf := share_lower f
    simp only [total]
    omega

/-- The abstract scaled form of q(x)<=21*a(x).
    1260*a = 1260*alpha + sum share; 60*q has the displayed value.
    The geometric proofs realizing the premises remain separate. -/
theorem scaled_score_lower (alpha e3 occupancy : Nat) (xs : List Fibre)
    (emptyCubeIdentity : total deficit xs = 3 * e3)
    (occupancyIdentity : total bonus xs = occupancy) :
    60 * (21 * alpha + 2 * xs.length + e3 + occupancy) ≤
      1260 * alpha + total share xs := by
  have hs := support_identity xs
  have hl := total_lower xs
  omega

/-- Global per-empty-face lemma. Each ni counts mothers with exactly i points.
    Multiplication by three avoids rational rounding. Zero mothers are allowed.
    An empty face contributes zero when h=0. -/
theorem global_fibre_budget : ∀ n1 n2 n3 : Fin 8,
    n1.val + n2.val + n3.val ≤ 7 →
    (13 - (n1.val + n2.val + n3.val)) *
      (n1.val + 2 * n2.val + 3 * n3.val) +
      12 * n1.val + 6 * n2.val ≤
    (if n1.val + n2.val + n3.val = 0 then 0 else 126) := by
  decide +kernel

#print axioms share_exact
#print axioms share_lower_table
#print axioms share_lower
#print axioms support_identity
#print axioms total_lower
#print axioms scaled_score_lower
#print axioms global_fibre_budget
end Q9Charge
