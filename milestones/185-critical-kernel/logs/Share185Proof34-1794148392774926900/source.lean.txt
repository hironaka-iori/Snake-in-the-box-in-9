import Share185Proof33
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sum_map_le {α : Type} {f g : α → Nat} : ∀ {l : List α}, (∀ a ∈ l, f a ≤ g a) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := sum_map_le (l := l) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega


end Snake9.LocalWindow.Tags185
