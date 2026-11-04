set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Snake9.CornerLoss166Core
theorem degree_decomposition : ∀ d : Fin 10, ∀ e : Fin 37,
    e.val ≤ (9 - d.val) * (8 - d.val) / 2 →
    (if d.val = 0 then 12 * e.val else (12 * e.val) % d.val) =
    (if d.val = 0 then 12 * e.val else if d.val = 5 then (2 * e.val) % 5
      else if d.val = 7 then 5 * e.val else 0) := by decide

theorem degree_five_table : ∀ e : Fin 7,
    (2 * e.val) % 5 =
      (if e.val = 1 ∨ e.val = 6 then 2 else if e.val = 2 then 4
       else if e.val = 3 then 1 else if e.val = 4 then 3 else 0) := by decide

theorem small_loss_zero_degree : ∀ e : Fin 37, ∀ loss : Fin 4,
    12 * e.val ≤ loss.val → e.val = 0 := by decide

theorem small_loss_degree_seven : ∀ e : Fin 2, ∀ loss : Fin 4,
    5 * e.val ≤ loss.val → e.val = 0 := by decide

theorem small_loss_degree_five : ∀ e : Fin 7, ∀ loss : Fin 4,
    (2 * e.val) % 5 ≤ loss.val → e.val ≠ 2 := by decide

theorem zero_loss_degree_five : ∀ e : Fin 7,
    (2 * e.val) % 5 = 0 → e.val = 0 ∨ e.val = 5 := by decide

#print axioms degree_decomposition
#print axioms degree_five_table
#print axioms small_loss_zero_degree
#print axioms small_loss_degree_seven
#print axioms small_loss_degree_five
#print axioms zero_loss_degree_five
end Snake9.CornerLoss166Core
