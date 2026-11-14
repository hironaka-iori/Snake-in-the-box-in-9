import Std
namespace FiniteDomain205
def edge (rows : Array Nat) (a b : Nat) : Bool := rows[a]!.testBit b
theorem exclude (ys : List Nat) (rel : Nat → Nat → Bool) (a b v : Nat)
    (hy : b ∈ ys) (compatible : rel a b=true)
    (blocked : ys.all (fun y => !(rel v y))=true) : a≠v := by
  intro same
  subst a
  have h := (List.all_eq_true.mp blocked) b hy
  simp [compatible] at h
theorem remove (x v : Nat) (xs : List Nat) (hx : x ∈ xs) (different : x≠v) :
    x ∈ xs.erase v := (List.mem_erase_of_ne different).mpr hx
theorem forced (x v : Nat) (h : x ∈ [v]) : x=v := List.mem_singleton.mp h
theorem impossible (x : Nat) (h : x ∈ ([] : List Nat)) : False := List.not_mem_nil h
#print axioms exclude
#print axioms remove
#print axioms forced
#print axioms impossible
end FiniteDomain205
