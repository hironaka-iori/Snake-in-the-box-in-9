import Snake9

/- Parity obstruction for internal rewiring (report Proposition 4.1, Corollary 4.2).

Every edge of the cube flips the parity of the number of one bits, so the parity of
the two endpoints of a snake determines the parity of its length.  Rewiring the
interior of a snake keeps both endpoints, hence keeps the parity of the length:
no 192-edge snake has the same two endpoints as a 191-edge snake. -/
namespace Snake9

set_option maxRecDepth 100000

/-- Parity of the number of one bits among the nine coordinates. -/
def bitParity (v : Nat) : Bool :=
  ((List.range 9).countP (fun k => v.testBit k)) % 2 == 1

theorem bitParity_flip : ∀ v : Fin 512, ∀ k : Fin 9,
    bitParity (Nat.xor v.val (2 ^ k.val)) = !bitParity v.val := by
  decide

theorem adj_flips_parity {u v : Vertex} (h : Adj u v) :
    bitParity v.val = !bitParity u.val := by
  obtain ⟨k, hk, he⟩ := (adj_iff_coordinate_flip u v).mp h
  rw [he]
  exact bitParity_flip u ⟨k, hk⟩

theorem parity_along {m : Nat} (p : Snake m) :
    ∀ n (h : n ≤ m), bitParity (p.vertex ⟨n, by omega⟩).val =
      (bitParity (p.vertex ⟨0, by omega⟩).val ^^ (n % 2 == 1)) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have hadj : Adj (p.vertex ⟨n, by omega⟩) (p.vertex ⟨n + 1, by omega⟩) :=
      (p.induced ⟨n, by omega⟩ ⟨n + 1, by omega⟩ (by simp)).mpr rfl
    rw [adj_flips_parity hadj, ih (by omega)]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have : (n + 1) % 2 = 1 := by omega
      simp [hn, this]
    · have : (n + 1) % 2 = 0 := by omega
      simp [hn, this]

/-- The endpoints of a snake of length `m` have equal parity exactly when `m` is even. -/
theorem endpoint_parity {m : Nat} (p : Snake m) :
    bitParity (p.vertex (Fin.last m)).val =
      (bitParity (p.vertex 0).val ^^ (m % 2 == 1)) :=
  parity_along p m (Nat.le_refl m)

/-- Two snakes with the same pair of endpoints have lengths of the same parity. -/
theorem same_endpoints_same_parity {m m' : Nat} (p : Snake m) (q : Snake m')
    (h0 : p.vertex 0 = q.vertex 0) (h1 : p.vertex (Fin.last m) = q.vertex (Fin.last m')) :
    m % 2 = m' % 2 := by
  have ep := endpoint_parity p
  have eq := endpoint_parity q
  rw [h0, h1, eq] at ep
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one m' with hm' | hm' <;>
    simp_all

/-- Corollary 4.2: internal rewiring of a 191-edge snake never gives 192 edges, because
it keeps both endpoints. -/
theorem no_192_with_endpoints_of_191 (p : Snake 191) (q : Snake 192)
    (h0 : p.vertex 0 = q.vertex 0) (h1 : p.vertex (Fin.last 191) = q.vertex (Fin.last 192)) :
    False := by
  have := same_endpoints_same_parity p q h0 h1
  omega

#print axioms bitParity_flip
#print axioms endpoint_parity
#print axioms same_endpoints_same_parity
#print axioms no_192_with_endpoints_of_191
end Snake9
