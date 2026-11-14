import ConcreteSupport213
import PathParity214
import TightPartner214

/-!
Source prepared for checking; not compiled by its author.
Normalization and bounded raw values derive actual parity-pool membership.
The current domains, candidate partners and support remain explicit.
-/

set_option Elab.async false

namespace PathTight214

open ConcreteGeometry213 IndexedCriterion206

private theorem even_pool_membership (values : Nat → Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ ConcreteSupport213.word (values (group i))))
    (hzero : values 0 = 0)
    (hbounded : ∀ g, g < 78 → values g < 64) :
    ∀ g, g ∈ chosen0 ++ outside0 → values g ∈ ConcreteParity214.pool false := by
  have hc : (chosen0 ++ outside0).all
      (fun g => decide (g < 78 ∧ g % 2 = 0)) = true := by
    decide +kernel
  intro g hg
  have hd := List.all_eq_true.mp hc g hg
  have hi : g < 78 ∧ g % 2 = 0 := by simpa using hd
  have hm := PathParity214.normalized_pool_membership values hp hzero hbounded g hi.1
  simpa [hi.2] using hm

private theorem odd_pool_membership (values : Nat → Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ ConcreteSupport213.word (values (group i))))
    (hzero : values 0 = 0)
    (hbounded : ∀ g, g < 78 → values g < 64) :
    ∀ g, g ∈ chosen1 ++ outside1 → values g ∈ ConcreteParity214.pool true := by
  have hc : (chosen1 ++ outside1).all
      (fun g => decide (g < 78 ∧ g % 2 = 1)) = true := by
    decide +kernel
  intro g hg
  have hd := List.all_eq_true.mp hc g hg
  have hi : g < 78 ∧ g % 2 = 1 := by simpa using hd
  have hm := PathParity214.normalized_pool_membership values hp hzero hbounded g hi.1
  simpa [hi.2] using hm

/-- An even tight subset reserves its candidate partners and the two
spare words. Support outside those partners preserves any other outside
variable's value in the same normalized indexed path assignment. -/
theorem even_normalized_path_tight_filter
    (J N support : List Nat) (chosen : Nat)
    (values : Nat → Nat) (domains : Nat → List Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ ConcreteSupport213.word (values (group i))))
    (hzero : values 0 = 0)
    (hbounded : ∀ g, g < 78 → values g < 64)
    (hJ : (J.map values).Nodup)
    (hJO : ∀ i, i ∈ J → i ∈ outside0)
    (hfit : ∀ i, values i ∈ domains i)
    (hN : ∀ i, i ∈ J → ∀ c, c ∈ chosen0 → c ∈ partners i →
      (∃ w, w ∈ domains i ∧ w ∈ domains c) → c ∈ N)
    (htight : J.length = N.length + 2)
    (hchosen : chosen ∈ outside0)
    (hchosenJ : chosen ∉ J)
    (hsupport : ∀ c, c ∈ chosen0 → c ∈ partners chosen → c ∉ N →
      ∀ w, w ∈ domains c → w ∈ support) :
    ∀ g, values g ∈
      (if g = chosen then
        (domains g).filter (fun w => decide (w ∈ support))
      else domains g) := by
  obtain ⟨hC, hO, hpartners⟩ := ConcreteSupport213.even_support_conditions values hp
  have hm := even_pool_membership values hp hzero hbounded
  have hCpool : ∀ c, c ∈ chosen0 → values c ∈ ConcreteParity214.pool false := by
    intro c hc
    exact hm c (List.mem_append.mpr (Or.inl hc))
  have hOpool : ∀ i, i ∈ outside0 → values i ∈ ConcreteParity214.pool false := by
    intro i hi
    exact hm i (List.mem_append.mpr (Or.inr hi))
  have hclength : chosen0.length = 30 := by decide +kernel
  have hplength := ConcreteParity214.pool_lengths.1
  have hsaturated :
      J.length = N.length + ((ConcreteParity214.pool false).length - chosen0.length) := by
    omega
  exact TightPartner214.tight_partner_filter_preserves_assignment
    chosen0 outside0 (ConcreteParity214.pool false) J N support chosen
    values domains partners hC hO hJ hCpool hOpool hJO hfit hpartners hN
    hsaturated hchosen hchosenJ hsupport

/-- The odd family has six spare words; the corresponding tight subset
supports the same assignment-preserving filter. -/
theorem odd_normalized_path_tight_filter
    (J N support : List Nat) (chosen : Nat)
    (values : Nat → Nat) (domains : Nat → List Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ ConcreteSupport213.word (values (group i))))
    (hzero : values 0 = 0)
    (hbounded : ∀ g, g < 78 → values g < 64)
    (hJ : (J.map values).Nodup)
    (hJO : ∀ i, i ∈ J → i ∈ outside1)
    (hfit : ∀ i, values i ∈ domains i)
    (hN : ∀ i, i ∈ J → ∀ c, c ∈ chosen1 → c ∈ partners i →
      (∃ w, w ∈ domains i ∧ w ∈ domains c) → c ∈ N)
    (htight : J.length = N.length + 6)
    (hchosen : chosen ∈ outside1)
    (hchosenJ : chosen ∉ J)
    (hsupport : ∀ c, c ∈ chosen1 → c ∈ partners chosen → c ∉ N →
      ∀ w, w ∈ domains c → w ∈ support) :
    ∀ g, values g ∈
      (if g = chosen then
        (domains g).filter (fun w => decide (w ∈ support))
      else domains g) := by
  obtain ⟨hC, hO, hpartners⟩ := ConcreteSupport213.odd_support_conditions values hp
  have hm := odd_pool_membership values hp hzero hbounded
  have hCpool : ∀ c, c ∈ chosen1 → values c ∈ ConcreteParity214.pool true := by
    intro c hc
    exact hm c (List.mem_append.mpr (Or.inl hc))
  have hOpool : ∀ i, i ∈ outside1 → values i ∈ ConcreteParity214.pool true := by
    intro i hi
    exact hm i (List.mem_append.mpr (Or.inr hi))
  have hclength : chosen1.length = 26 := by decide +kernel
  have hplength := ConcreteParity214.pool_lengths.2
  have hsaturated :
      J.length = N.length + ((ConcreteParity214.pool true).length - chosen1.length) := by
    omega
  exact TightPartner214.tight_partner_filter_preserves_assignment
    chosen1 outside1 (ConcreteParity214.pool true) J N support chosen
    values domains partners hC hO hJ hCpool hOpool hJO hfit hpartners hN
    hsaturated hchosen hchosenJ hsupport

#print axioms even_normalized_path_tight_filter
#print axioms odd_normalized_path_tight_filter

end PathTight214
