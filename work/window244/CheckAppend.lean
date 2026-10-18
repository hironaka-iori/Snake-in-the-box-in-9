import LratCheck

namespace Snake9.Lrat
set_option Elab.async false

noncomputable def advanceChecks (t : Tree) (xs : List Nat) : Tree := xs.foldl ins t

theorem check_append_exact (t : Tree) (xs ys : List Nat) :
    check t (xs ++ ys) = andB (check t xs) (check (advanceChecks t xs) ys) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    change andB (rup t x) (check (ins t x) (xs ++ ys)) =
      andB (andB (rup t x) (check (ins t x) xs))
        (check (advanceChecks (ins t x) xs) ys)
    rw [ih]
    cases rup t x <;> rfl

theorem check_append_true (t : Tree) (xs ys : List Nat)
    (ha : check t xs = true) (hb : check (advanceChecks t xs) ys = true) :
    check t (xs ++ ys) = true := by
  rw [check_append_exact, ha, hb]
  rfl
end Snake9.Lrat
