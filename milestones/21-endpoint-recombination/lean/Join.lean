import Snake9
import Mathlib.Tactic

namespace Snake9.Recombination

def joinVertex {m n : Nat} (p : Snake m) (q : Snake n)
    (i : Fin (m + n + 1)) : Vertex :=
  if h : i.val ≤ m then p.vertex ⟨i.val, by omega⟩
  else q.vertex ⟨i.val - m, by omega⟩

/-- Exact cross conditions sufficient to join two induced paths at one vertex. -/
def join {m n : Nat} (p : Snake m) (q : Snake n)
    (separate : ∀ i j, 0 < j.val → p.vertex i ≠ q.vertex j)
    (cross : ∀ i j, 0 < j.val →
      (Adj (p.vertex i) (q.vertex j) ↔ i.val = m ∧ j.val = 1)) : Snake (m+n) where
  vertex := joinVertex p q
  distinct i j he := by
    unfold joinVertex at he
    split_ifs at he with hi hj hj
    · have h := p.distinct _ _ he
      apply Fin.ext
      exact congrArg (fun t : Fin (m+1) => t.val) h
    · exact False.elim (separate _ _ (by dsimp; omega) he)
    · exact False.elim (separate _ _ (by dsimp; omega) he.symm)
    · have h := q.distinct _ _ he
      have hv := congrArg Fin.val h
      apply Fin.ext
      simp only at hv
      omega
  induced i j hij := by
    unfold joinVertex
    split_ifs with hi hj hj
    · exact p.induced _ _ hij
    · rw [cross _ _ (by dsimp; omega)]
      simp only
      omega
    · omega
    · rw [q.induced _ _ (by dsimp; omega)]
      simp only
      omega

theorem join_start {m n : Nat} (p : Snake m) (q : Snake n)
    (hd : ∀ i j, 0 < j.val → p.vertex i ≠ q.vertex j)
    (hc : ∀ i j, 0 < j.val →
      (Adj (p.vertex i) (q.vertex j) ↔ i.val = m ∧ j.val = 1)) :
    (join p q hd hc).vertex 0 = p.vertex 0 := by
  simp [join,joinVertex]

theorem join_end {m n : Nat} (p : Snake m) (q : Snake n)
    (hn : 0 < n)
    (hd : ∀ i j, 0 < j.val → p.vertex i ≠ q.vertex j)
    (hc : ∀ i j, 0 < j.val →
      (Adj (p.vertex i) (q.vertex j) ↔ i.val = m ∧ j.val = 1)) :
    (join p q hd hc).vertex (Fin.last (m+n)) = q.vertex (Fin.last n) := by
  simp only [join,joinVertex,Fin.val_last,show ¬m+n≤m by omega,dif_neg,Nat.add_sub_cancel_left]
  congr 1

theorem stabilizer_size : Nat.factorial 4 * Nat.factorial 5 * 2 = 5760 := by decide

#print axioms join
#print axioms join_start
#print axioms join_end
#print axioms stabilizer_size
end Snake9.Recombination
