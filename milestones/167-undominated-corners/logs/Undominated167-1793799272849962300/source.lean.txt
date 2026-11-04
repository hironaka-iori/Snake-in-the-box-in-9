set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Snake9.Undominated167
-- P records selected pair vertices; T records selected triple vertices.
-- These local implications still require their Q9 interpretation.
theorem no_two_unused {I : Type} (P : I → I → Prop) (T : I → I → I → Prop)
    (minimum : ∀ a b, a ≠ b → P a b →
      ∃ k, k ≠ a ∧ k ≠ b ∧ T a b k)
    (maximum : ∀ a b k, a ≠ b → k ≠ a → k ≠ b →
      T a b k → P a b → P a k → P b k → False)
    (a b : I) (hab : a ≠ b)
    (ha : ∀ k, k ≠ a → P a k)
    (hb : ∀ k, k ≠ b → P b k) : False := by
  have hba : b ≠ a := fun h => hab h.symm
  have hp := ha b hba
  cases minimum a b hab hp with
  | intro k hk =>
    exact maximum a b k hab hk.1 hk.2.1 hk.2.2 hp
      (ha k hk.1) (hb k hk.2.1)

theorem matching_forces_unique_neighbor {I : Type}
    (P : I → I → Prop) (T : I → I → I → Prop)
    (minimum : ∀ a b, a ≠ b → P a b →
      ∃ k, k ≠ a ∧ k ≠ b ∧ T a b k)
    (maximum : ∀ a b k, a ≠ b → k ≠ a → k ≠ b →
      T a b k → P a b → P a k → P b k → False)
    (c a partner : I) (hca : c ≠ a)
    (hc : ∀ k, k ≠ c → P c k)
    (ha : ∀ k, k ≠ a → k ≠ partner → P a k) :
    T c a partner ∧
      ∀ k, k ≠ c → k ≠ a → T c a k → k = partner := by
  have hac : a ≠ c := fun h => hca h.symm
  have hp := hc a hac
  have unique : ∀ k, k ≠ c → k ≠ a → T c a k → k = partner := by
    intro k hkc hka ht
    exact Classical.byContradiction (fun hkp =>
      maximum c a k hca hkc hka ht hp (hc k hkc) (ha k hka hkp))
  cases minimum c a hca hp with
  | intro k hk =>
    have heq := unique k hk.1 hk.2.1 hk.2.2
    exact ⟨heq ▸ hk.2.2, unique⟩

-- Incidence arithmetic: nine directions, at most one unused, two per pair.
theorem incidence_lower_bound : ∀ e : Fin 37, ∀ covered : Fin 10,
    8 ≤ covered.val → covered.val ≤ 2 * e.val → 4 ≤ e.val := by decide

theorem equality_coverage : ∀ covered : Fin 10,
    8 ≤ covered.val → covered.val ≤ 2 * 4 → covered.val = 8 := by decide

theorem endpoint_exclusion : ∀ endpoints : Fin 513,
    8 ≤ endpoints.val → endpoints.val ≤ 2 → False := by decide

theorem loss_from_undominated : ∀ e : Fin 37, ∀ loss : Fin 60,
    5 ≤ e.val → 12 * e.val ≤ loss.val → False := by decide

#print axioms no_two_unused
#print axioms matching_forces_unique_neighbor
#print axioms incidence_lower_bound
#print axioms equality_coverage
#print axioms endpoint_exclusion
#print axioms loss_from_undominated
end Snake9.Undominated167
