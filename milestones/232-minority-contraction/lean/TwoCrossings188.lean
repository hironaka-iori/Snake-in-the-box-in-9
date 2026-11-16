import LayerJoining
namespace Dimensional188
open LayerJoining

def appendVertex {V : Type} {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b)
    (i : Fin (a+b+2)) : V :=
  if h : i.val ≤ a then p.vertex ⟨i.val,by omega⟩
  else q.vertex ⟨i.val-(a+1),by omega⟩

def appendEdge {V : Type} {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b)
    (hdis : ∀ i j, p.vertex i ≠ q.vertex j)
    (hcross : ∀ i j, R (p.vertex i) (q.vertex j) ↔ i.val=a ∧ j.val=0) :
    InducedPath V R (a+b+1) where
  vertex := appendVertex p q
  distinct i j he := by
    unfold appendVertex at he
    split at he <;> split at he
    · have h := p.distinct _ _ he
      apply Fin.ext
      exact congrArg (fun z : Fin (a+1) => z.val) h
    · exact False.elim (hdis _ _ he)
    · exact False.elim (hdis _ _ he.symm)
    · have h := q.distinct _ _ he
      have hv := congrArg Fin.val h
      apply Fin.ext
      simp only at hv
      omega
  induced i j hij := by
    unfold appendVertex
    split <;> split
    · exact p.induced _ _ hij
    · rw [hcross]
      simp only [Fin.val_mk]
      omega
    · omega
    · rw [q.induced _ _ (by simp only; omega)]
      simp only [Fin.val_mk]
      omega

def inLayer {V : Type} {R : V → V → Prop} {a : Nat}
    (p : InducedPath V R a) (side : Bool) :
    InducedPath (V × Bool) (LayerAdj R) a where
  vertex i := (p.vertex i,side)
  distinct i j he := p.distinct i j (congrArg Prod.fst he)
  induced i j hij := by simpa [LayerAdj] using p.induced i j hij

def twoCrossings {V : Type} {R : V → V → Prop} {a b c : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b) (r : InducedPath V R c)
    (hpq : Compatible p q) (hqr : Compatible q r)
    (hpr : ∀ i j, p.vertex i ≠ r.vertex j ∧ ¬ R (p.vertex i) (r.vertex j)) :
    InducedPath (V × Bool) (LayerAdj R) (a+b+c+2) := by
  have hd : ∀ i j, (join p q hpq).vertex i ≠ (inLayer r false).vertex j := by
    intro i j
    change joinedVertex p q i ≠ (r.vertex j,false)
    unfold joinedVertex
    split
    · intro he
      exact (hpr _ _).1 (congrArg Prod.fst he)
    · intro he
      have h := congrArg Prod.snd he
      simp at h
  have hc : ∀ i j, LayerAdj R ((join p q hpq).vertex i) ((inLayer r false).vertex j)
      ↔ i.val=a+b+1 ∧ j.val=0 := by
    intro i j
    change LayerAdj R (joinedVertex p q i) (r.vertex j,false) ↔ _
    unfold joinedVertex
    split
    · simp only [LayerAdj, true_and, ne_eq, not_true_eq_false, false_and, or_false]
      have hn := (hpr ⟨i.val,by omega⟩ j).2
      constructor
      · intro h; exact False.elim (hn h)
      · intro h; omega
    · simp only [LayerAdj, Bool.true_eq_false, false_and, ne_eq,
        not_false_eq_true, true_and, false_or]
      rw [hqr]
      simp only [Fin.val_mk]
      omega
  have t := appendEdge (join p q hpq) (inLayer r false) hd hc
  have he : (a+b+1)+c+1=a+b+c+2 := by omega
  simpa only [he] using t

theorem target194 (a b c : Nat) (h : a+b+c=192) : a+b+c+2=194 := by omega

#print axioms appendEdge
#print axioms inLayer
#print axioms twoCrossings
#print axioms target194
end Dimensional188
