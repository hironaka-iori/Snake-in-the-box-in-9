import Snake9

namespace Snake9

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Every candidate adjacent to the last vertex is blocked by an earlier vertex. -/
def RightBlocked (p : Snake 191) : Prop :=
  ∀ w : Vertex, Adj (p.vertex ⟨191, by decide⟩) w →
    ∃ i : Fin 191,
      p.vertex ⟨i.val, by omega⟩ = w ∨ Adj (p.vertex ⟨i.val, by omega⟩) w

theorem prefix192_not_blocked (q : Snake 192) :
    ¬ RightBlocked (takePrefix q (by decide : 191 ≤ 192)) := by
  intro hb
  have ha : Adj (q.vertex ⟨191, by decide⟩) (q.vertex ⟨192, by decide⟩) :=
    (q.induced ⟨191, by decide⟩ ⟨192, by decide⟩ (by decide)).mpr rfl
  obtain ⟨i, hi⟩ := hb (q.vertex ⟨192, by decide⟩) ha
  have hiBound := i.isLt
  cases hi with
  | inl he =>
    have eq := q.distinct ⟨i.val, by omega⟩ ⟨192, by decide⟩ he
    have hv := congrArg (fun z : Fin 193 => z.val) eq
    change i.val = 192 at hv
    omega
  | inr he =>
    have hv := (q.induced ⟨i.val, by omega⟩ ⟨192, by decide⟩ (by change i.val < 192; omega)).mp he
    change i.val + 1 = 192 at hv
    omega

theorem all191_blocked_implies_optimal
    (h : ∀ p : Snake 191, RightBlocked p) :
    Nonempty (Snake 191) ∧ (∀ m, Nonempty (Snake m) → m ≤ 191) := by
  apply optimality_of_no192
  intro ht
  obtain ⟨q⟩ := target192_iff.mp ht
  exact prefix192_not_blocked q (h (takePrefix q (by decide)))

def endpointCandidate (k : Fin 9) : Vertex :=
  ⟨(Nat.xor 118 (2 ^ k.val)) % 512, Nat.mod_lt _ (by decide)⟩

def blockerIndex (k : Fin 9) : Fin 191 :=
  ⟨(#[19,37,13,13,27,19,189,43,91] : Array Nat)[k.val]! % 191,
   Nat.mod_lt _ (by decide)⟩

theorem candidate_value : ∀ k : Fin 9,
    (endpointCandidate k).val = Nat.xor (witness.vertex ⟨191, by decide⟩).val (2 ^ k.val) := by
  decide

theorem candidate_blockers : ∀ k : Fin 9,
    witness.vertex ⟨(blockerIndex k).val, by omega⟩ = endpointCandidate k ∨
    Adj (witness.vertex ⟨(blockerIndex k).val, by omega⟩) (endpointCandidate k) := by
  decide

theorem witness_right_blocked : RightBlocked witness := by
  intro w ha
  obtain ⟨k, hk, he⟩ := (adj_iff_coordinate_flip _ _).mp ha
  let a : Fin 9 := ⟨k, hk⟩
  have hw : w = endpointCandidate a := by
    apply Fin.ext
    exact he.trans (candidate_value a).symm
  rw [hw]
  exact ⟨blockerIndex a, candidate_blockers a⟩

#print axioms prefix192_not_blocked
#print axioms all191_blocked_implies_optimal
#print axioms witness_right_blocked
end Snake9
