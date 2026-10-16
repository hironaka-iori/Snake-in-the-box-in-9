import DfsCertificate

namespace Snake9

/-- Reversal preserves inducedness, with the same edge count. -/
def reverseSnake {m : Nat} (p : Snake m) : Snake m where
  vertex i := p.vertex ⟨m - i.val, by omega⟩
  distinct i j h := by
    have e := p.distinct ⟨m-i.val, by omega⟩ ⟨m-j.val, by omega⟩ h
    have := congrArg Fin.val e
    apply Fin.ext
    simp only at this
    omega
  induced i j hij := by
    have hs {u v : Vertex} (h : Adj u v) : Adj v u := by
      obtain ⟨k, hk, he⟩ := (adj_iff_coordinate_flip u v).mp h
      apply (adj_iff_coordinate_flip v u).mpr
      refine ⟨k, hk, ?_⟩
      rw [he]
      change u.val = (u.val ^^^ 2^k) ^^^ 2^k
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have hp := p.induced ⟨m-j.val, by omega⟩ ⟨m-i.val, by omega⟩ (by simp; omega)
    constructor
    · intro h
      have := hp.mp (hs h)
      simp only at this
      omega
    · intro h
      apply hs
      apply hp.mpr
      simp only
      omega

namespace Dfs

def StartsWith {m : Nat} (p : Snake m) (pre : Array Nat) (K : Nat) : Prop :=
  ∀ i, i < K → ∀ hi : i < m+1, (p.vertex ⟨i,hi⟩).val = pre[i]!

/-- End segments are read from the final endpoint inward. -/
def EndsWith {m : Nat} (p : Snake m) (pre : Array Nat) (K : Nat) : Prop :=
  StartsWith (reverseSnake p) pre K

/-- A 192-edge prefix exclusion also excludes every longer snake with that prefix. -/
theorem prefix_exclusion_all_lengths (pre : Array Nat) (K : Nat) (hK : K ≤ 193)
    (hex : ¬ ∃ p : Snake 192, ∀ i (hi : i<K), (p.vertex ⟨i,by omega⟩).val = pre[i]!)
    {m : Nat} (hm : 192 ≤ m) (p : Snake m) : ¬ StartsWith p pre K := by
  intro h
  apply hex
  refine ⟨takePrefix p hm, ?_⟩
  intro i hi
  exact h i hi (by omega)

/-- The same certificate excludes end segments of every snake of at least 192 edges. -/
theorem suffix_exclusion_all_lengths (pre : Array Nat) (K : Nat) (hK : K ≤ 193)
    (hex : ¬ ∃ p : Snake 192, ∀ i (hi : i<K), (p.vertex ⟨i,by omega⟩).val = pre[i]!)
    {m : Nat} (hm : 192 ≤ m) (p : Snake m) : ¬ EndsWith p pre K :=
  prefix_exclusion_all_lengths pre K hK hex hm (reverseSnake p)

#print axioms reverseSnake
#print axioms prefix_exclusion_all_lengths
#print axioms suffix_exclusion_all_lengths
end Dfs
end Snake9
