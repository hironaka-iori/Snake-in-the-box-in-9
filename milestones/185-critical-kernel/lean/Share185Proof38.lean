import Share185Proof37
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem capL_le : ∀ (cens : List Centre) (spec : List (List (Nat × Nat))),
    (∀ s ∈ spec, subl (s.map (·.1)) (List.range 9) = true) →
    (capL cens spec).countP (fun p => decide (p.2 ≤ fl Mr S p.1)) ≤ shareSum Mr S cens
  | [], _, _ => by simp [capL]
  | _ :: _, [], _ => by simp [capL]
  | c :: cens, s :: spec, hs => by
    simp only [capL]
    rw [List.countP_append, shareSum_cons]
    have ih := capL_le cens spec (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
    have h1 : (s.flatMap fun kt => (List.range kt.2).map fun t => (c.v ^^^ (1 <<< kt.1), t + 1)).countP
        (fun p => decide (p.2 ≤ fl Mr S p.1)) ≤
        ((s.map (·.1)).map fun k => fl Mr S (c.v ^^^ (1 <<< k))).sum := by
      rw [List.countP_flatMap, List.map_map]
      apply sum_map_le
      intro kt _
      simp only [Function.comp, List.countP_map]
      exact countP_range_le (fl Mr S (c.v ^^^ 1 <<< kt.1)) kt.2
    have h2 := sum_sublist_le ((subl_sublist (hs s List.mem_cons_self)).map
      (fun k => fl Mr S (c.v ^^^ (1 <<< k))))
    rw [shareLocal_fl]
    omega


end Snake9.LocalWindow.Tags185
