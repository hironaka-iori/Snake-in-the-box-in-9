import ConcreteSupport213
import SupportBridge212

/-!
Source prepared for checking; not compiled by its author.
The actual-path premise discharges concrete distinctness and partner
completeness. Domain fitting, a 32-entry pool, and support containment
remain explicit. No native propagation or traversal is certified.
-/

set_option Elab.async false

namespace PathSupport213

open ConcreteGeometry213 ConcreteSupport213 IndexedCriterion206

/-- For the literal even family, two domain-forced exceptions exhaust
the spare capacity and justify support filtering at another outside index. -/
theorem even_path_support_filter
    (pool F : List Nat) (chosen : Nat)
    (values : Nat → Nat) (domains support : Nat → List Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ word (values (group i))))
    (hpool : pool.length = 32)
    (hdomains : ∀ i, i ∈ chosen0 ++ outside0 →
      ∀ w, w ∈ domains i → w ∈ pool)
    (hfit : ∀ i, values i ∈ domains i)
    (hF : F.Nodup)
    (hFoutside : ∀ i, i ∈ F → i ∈ outside0)
    (hforced : ∀ i, i ∈ F →
      ∀ w, w ∈ domains i → w ∉ support i)
    (hsupport : ∀ i, i ∈ outside0 → ∀ c, c ∈ partners i →
      ∀ w, w ∈ domains c → w ∈ support i)
    (hcount : F.length = 2)
    (hchosen : chosen ∈ outside0)
    (hnotforced : chosen ∉ F) :
    ∀ g, values g ∈
      (if g = chosen then
        (domains g).filter (fun w => decide (w ∈ support chosen))
      else domains g) := by
  obtain ⟨hC, hO, hpartners⟩ := even_support_conditions values hp
  have hclength : chosen0.length = 30 := by decide +kernel
  have hCpool : ∀ c, c ∈ chosen0 → values c ∈ pool := by
    intro c hc
    exact hdomains c (List.mem_append.mpr (Or.inl hc)) (values c) (hfit c)
  have hOpool : ∀ i, i ∈ outside0 → values i ∈ pool := by
    intro i hi
    exact hdomains i (List.mem_append.mpr (Or.inr hi)) (values i) (hfit i)
  have hsaturated : F.length = pool.length - chosen0.length := by omega
  exact SupportBridge212.saturated_support_preserves_assignment
    chosen0 outside0 pool F chosen values domains partners support
    hC hO hCpool hOpool hF hFoutside hforced hfit hpartners hsupport
    hsaturated hchosen hnotforced

/-- The corresponding odd family has six spare words, so six
domain-forced exceptions justify the same support-filter deduction. -/
theorem odd_path_support_filter
    (pool F : List Nat) (chosen : Nat)
    (values : Nat → Nat) (domains support : Nat → List Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ word (values (group i))))
    (hpool : pool.length = 32)
    (hdomains : ∀ i, i ∈ chosen1 ++ outside1 →
      ∀ w, w ∈ domains i → w ∈ pool)
    (hfit : ∀ i, values i ∈ domains i)
    (hF : F.Nodup)
    (hFoutside : ∀ i, i ∈ F → i ∈ outside1)
    (hforced : ∀ i, i ∈ F →
      ∀ w, w ∈ domains i → w ∉ support i)
    (hsupport : ∀ i, i ∈ outside1 → ∀ c, c ∈ partners i →
      ∀ w, w ∈ domains c → w ∈ support i)
    (hcount : F.length = 6)
    (hchosen : chosen ∈ outside1)
    (hnotforced : chosen ∉ F) :
    ∀ g, values g ∈
      (if g = chosen then
        (domains g).filter (fun w => decide (w ∈ support chosen))
      else domains g) := by
  obtain ⟨hC, hO, hpartners⟩ := odd_support_conditions values hp
  have hclength : chosen1.length = 26 := by decide +kernel
  have hCpool : ∀ c, c ∈ chosen1 → values c ∈ pool := by
    intro c hc
    exact hdomains c (List.mem_append.mpr (Or.inl hc)) (values c) (hfit c)
  have hOpool : ∀ i, i ∈ outside1 → values i ∈ pool := by
    intro i hi
    exact hdomains i (List.mem_append.mpr (Or.inr hi)) (values i) (hfit i)
  have hsaturated : F.length = pool.length - chosen1.length := by omega
  exact SupportBridge212.saturated_support_preserves_assignment
    chosen1 outside1 pool F chosen values domains partners support
    hC hO hCpool hOpool hF hFoutside hforced hfit hpartners hsupport
    hsaturated hchosen hnotforced

#print axioms even_path_support_filter
#print axioms odd_path_support_filter

end PathSupport213
