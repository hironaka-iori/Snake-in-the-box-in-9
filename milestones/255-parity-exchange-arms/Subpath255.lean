import LayerJoining

namespace Subpath255
open LayerJoining

variable {V : Type} {R : V → V → Prop} {m n : Nat}

def shiftIndex {s k n : Nat} (bound : s + k ≤ n) (i : Fin (k + 1)) : Fin (n + 1) :=
  ⟨s + i.val, by have hi := i.isLt; omega⟩

/-- The consecutive interval of k edges beginning at index s. -/
def window {s k : Nat} (q : InducedPath V R n) (bound : s + k ≤ n) : InducedPath V R k where
  vertex i := q.vertex (shiftIndex bound i)
  distinct i j h := by
    have eq := congrArg Fin.val (q.distinct (shiftIndex bound i) (shiftIndex bound j) h)
    change s + i.val = s + j.val at eq
    apply Fin.ext
    omega
  induced i j h := by
    have lt : (shiftIndex bound i).val < (shiftIndex bound j).val := by
      change s + i.val < s + j.val
      omega
    rw [q.induced _ _ lt]
    change (s + i.val + 1 = s + j.val) ↔ i.val + 1 = j.val
    omega

def Occurs (p : InducedPath V R m) (q : InducedPath V R n) : Prop :=
  ∃ (s : Nat) (bound : s + m ≤ n), ∀ i, p.vertex i = q.vertex (shiftIndex bound i)

/-- If there is room on the right, add the following edge. Otherwise add the preceding edge. -/
theorem one_edge_extension (p : InducedPath V R m) (q : InducedPath V R n)
    (occ : Occurs p q) (longer : m < n) :
    ∃ e : InducedPath V R (m+1), Occurs p e ∧ Occurs e q := by
  obtain ⟨s, bound, agrees⟩ := occ
  by_cases right : s + m < n
  · have big : s + (m+1) ≤ n := by omega
    refine ⟨window q big, ?_, ⟨s, big, fun _ => rfl⟩⟩
    have start : 0 + m ≤ m+1 := by omega
    refine ⟨0, start, ?_⟩
    intro i
    rw [agrees i]
    change q.vertex (shiftIndex bound i) = q.vertex (shiftIndex big (shiftIndex start i))
    apply congrArg q.vertex
    apply Fin.ext
    change s + i.val = s + (0 + i.val)
    omega
  · have big : (s-1) + (m+1) ≤ n := by omega
    refine ⟨window q big, ?_, ⟨s-1, big, fun _ => rfl⟩⟩
    have start : 1 + m ≤ m+1 := by omega
    refine ⟨1, start, ?_⟩
    intro i
    rw [agrees i]
    change q.vertex (shiftIndex bound i) = q.vertex (shiftIndex big (shiftIndex start i))
    apply congrArg q.vertex
    apply Fin.ext
    change s + i.val = (s-1) + (1 + i.val)
    omega

theorem unextendible_occurrence (p : InducedPath V R m) (q : InducedPath V R n)
    (occ : Occurs p q) (closed : ∀ e : InducedPath V R (m+1), ¬ Occurs p e) : m = n := by
  by_cases longer : m < n
  · obtain ⟨e, sits, _⟩ := one_edge_extension p q occ longer
    exact False.elim (closed e sits)
  · obtain ⟨s, bound, _⟩ := occ
    omega

#print axioms window
#print axioms one_edge_extension
#print axioms unextendible_occurrence

end Subpath255
