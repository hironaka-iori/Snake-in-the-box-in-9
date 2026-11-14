import LayerJoining
import WordParity214

set_option Elab.async false

namespace PartnerParity218
open LayerJoining IndexedCriterion206 WordParity214

/-- Consecutive adjacency of the actual 93-edge path fixes the parity at
every index once the initial vertex has even parity. -/
theorem index_parity
    (p : InducedPath (List Bool) (fun u v => hamming u v = 1) 93)
    (width : Nat) (lengths : ∀ i, (p.vertex i).length = width)
    (initial_even : parity (p.vertex ⟨0, by decide⟩) = false) :
    ∀ i : Fin 94, parity (p.vertex i) = decide (i.val % 2 = 1) := by
  have indexed : ∀ k (hk : k < 94),
      parity (p.vertex ⟨k, hk⟩) = decide (k % 2 = 1) := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa using initial_even
    | succ k ih =>
        intro hk
        have hprev : k < 94 := by omega
        have previous := ih hprev
        have adjacent : hamming (p.vertex ⟨k, hprev⟩)
            (p.vertex ⟨k + 1, hk⟩) = 1 := by
          exact (p.induced ⟨k, hprev⟩ ⟨k + 1, hk⟩ (by simp)).mpr rfl
        have flipped := adjacent_parity (p.vertex ⟨k, hprev⟩)
          (p.vertex ⟨k + 1, hk⟩) (by rw [lengths, lengths]) adjacent
        rw [previous] at flipped
        exact flipped.trans (index_parity_step k).symm
  intro i
  exact indexed i.val i.isLt

/-- The free second endpoint of this path has odd parity. -/
theorem last_is_odd
    (p : InducedPath (List Bool) (fun u v => hamming u v = 1) 93)
    (width : Nat) (lengths : ∀ i, (p.vertex i).length = width)
    (initial_even : parity (p.vertex ⟨0, by decide⟩) = false) :
    parity (p.vertex ⟨93, by decide⟩) = true := by
  have h := index_parity p width lengths initial_even ⟨93, by decide⟩
  simpa using h

/-- The 94 path vertices split into 47 vertices of each parity. -/
theorem colour_counts
    (p : InducedPath (List Bool) (fun u v => hamming u v = 1) 93)
    (width : Nat) (lengths : ∀ i, (p.vertex i).length = width)
    (initial_even : parity (p.vertex ⟨0, by decide⟩) = false) :
    (List.ofFn (fun i : Fin 94 => parity (p.vertex i))).count true = 47 ∧
    (List.ofFn (fun i : Fin 94 => parity (p.vertex i))).count false = 47 := by
  have same : (fun i : Fin 94 => parity (p.vertex i)) =
      (fun i : Fin 94 => decide (i.val % 2 = 1)) := by
    funext i
    exact index_parity p width lengths initial_even i
  rw [same]
  decide

#print axioms index_parity
#print axioms last_is_odd
#print axioms colour_counts
end PartnerParity218
