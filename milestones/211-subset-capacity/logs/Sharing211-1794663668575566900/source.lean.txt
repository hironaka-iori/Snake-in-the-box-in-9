import Spare211

namespace Sharing211

private theorem split_count (C O : List Nat) :
    (O.filter (fun w => C.contains w)).length +
    (O.filter (fun w => !(C.contains w))).length = O.length := by
  induction O with
  | nil => simp
  | cons w ws ih =>
    by_cases h : w ∈ C <;> simp [List.filter_cons, h] at * <;> omega

theorem forced_sharing (C O pool : List Nat)
    (hC : C.Nodup) (hO : O.Nodup)
    (hCpool : ∀ w, w ∈ C → w ∈ pool)
    (hOpool : ∀ w, w ∈ O → w ∈ pool) :
    C.length + O.length ≤ pool.length +
      (O.filter (fun w => C.contains w)).length := by
  have h := Spare211.spare_capacity C O pool hC hO hCpool hOpool
  have p := split_count C O
  omega

theorem one_of_two (shared : Nat) (h : 31 + 2 ≤ 32 + shared) :
    1 ≤ shared := by omega

theorem seven_of_nine (shared : Nat) (h : 30 + 9 ≤ 32 + shared) :
    7 ≤ shared := by omega

theorem seven_of_thirteen (shared : Nat) (h : 26 + 13 ≤ 32 + shared) :
    7 ≤ shared := by omega

#print axioms forced_sharing
#print axioms one_of_two
#print axioms seven_of_nine
#print axioms seven_of_thirteen
end Sharing211
