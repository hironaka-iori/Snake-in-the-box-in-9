import InputTree150Replay
import LocalWindowCnf.ShareWindow150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ReplayData150
open Snake9.ReplayInput150 (InputTree)

theorem all_take_drop {α : Type} (f : α → Bool) (xs : List α)
    (h : xs.all f = true) (offset count : Nat) :
    ((xs.drop offset).take count).all f = true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact List.all_eq_true.mp h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

theorem all_of_subset {α : Type} (f : α → Bool) {xs ys : List α}
    (h : xs.all f = true) (hs : ∀ x ∈ ys, x ∈ xs) : ys.all f = true := by
  exact List.all_eq_true.mpr (fun x hx => List.all_eq_true.mp h x (hs x hx))

theorem build_true_of_slice (τ : Nat → Bool) (t : InputTree)
    (xs : List (List Nat)) (offset count : Nat)
    (heq : t.clauses = (xs.drop offset).take count)
    (h : xs.all (fun c => Snake9.LocalWindow.clauseTrue τ
      (c.map Snake9.LocalWindow.decodeLit)) = true) :
    Snake9.Lrat150Replay.TreeTrue τ t.build := by
  apply t.build_true τ
  rw [List.all_map, heq]
  exact all_take_drop _ xs h offset count
#print axioms all_take_drop
#print axioms all_of_subset
#print axioms build_true_of_slice
end Snake9.ReplayData150
