import TwoCrossings188

set_option Elab.async false

namespace FourCrossings223
open LayerJoining Dimensional188

private theorem append_separated {V : Type} {R : V → V → Prop}
    {a b c : Nat} (p : InducedPath V R a) (q : InducedPath V R b)
    (r : InducedPath V R c)
    (disjoint : ∀ i j, p.vertex i ≠ q.vertex j)
    (contact : ∀ i j, R (p.vertex i) (q.vertex j) ↔ i.val = a ∧ j.val = 0)
    (pr : ∀ i j, p.vertex i ≠ r.vertex j ∧ ¬R (p.vertex i) (r.vertex j))
    (qr : ∀ i j, q.vertex i ≠ r.vertex j ∧ ¬R (q.vertex i) (r.vertex j)) :
    ∀ i j, (appendEdge p q disjoint contact).vertex i ≠ r.vertex j ∧
      ¬R ((appendEdge p q disjoint contact).vertex i) (r.vertex j) := by
  intro i j
  change appendVertex p q i ≠ r.vertex j ∧ ¬R (appendVertex p q i) (r.vertex j)
  unfold appendVertex
  split
  · exact pr _ j
  · exact qr _ j

private theorem append_last_contact {V : Type} {R : V → V → Prop}
    {a b c : Nat} (p : InducedPath V R a) (q : InducedPath V R b)
    (r : InducedPath V R c)
    (disjoint : ∀ i j, p.vertex i ≠ q.vertex j)
    (contact : ∀ i j, R (p.vertex i) (q.vertex j) ↔ i.val = a ∧ j.val = 0)
    (pr : ∀ i j, p.vertex i ≠ r.vertex j ∧ ¬R (p.vertex i) (r.vertex j))
    (qr_disjoint : ∀ i j, q.vertex i ≠ r.vertex j)
    (qr_contact : ∀ i j, R (q.vertex i) (r.vertex j) ↔ i.val = b ∧ j.val = 0) :
    (∀ i j, (appendEdge p q disjoint contact).vertex i ≠ r.vertex j) ∧
    (∀ i j, R ((appendEdge p q disjoint contact).vertex i) (r.vertex j) ↔
      i.val = a + b + 1 ∧ j.val = 0) := by
  constructor
  · intro i j
    change appendVertex p q i ≠ r.vertex j
    unfold appendVertex
    split
    · exact (pr _ j).1
    · exact qr_disjoint _ j
  · intro i j
    change R (appendVertex p q i) (r.vertex j) ↔ _
    unfold appendVertex
    split
    · constructor
      · intro edge
        exact False.elim ((pr _ j).2 edge)
      · intro ends
        omega
    · rw [qr_contact]
      simp only [Fin.val_mk]
      omega

private theorem same_layer_separated {V : Type} {R : V → V → Prop}
    {a b : Nat} (p : InducedPath V R a) (q : InducedPath V R b) (side : Bool)
    (separation : ∀ i j, p.vertex i ≠ q.vertex j ∧ ¬R (p.vertex i) (q.vertex j)) :
    ∀ i j, (inLayer p side).vertex i ≠ (inLayer q side).vertex j ∧
      ¬LayerAdj R ((inLayer p side).vertex i) ((inLayer q side).vertex j) := by
  intro i j
  constructor
  · intro equal
    exact (separation i j).1 (congrArg Prod.fst equal)
  · simpa [inLayer, LayerAdj] using (separation i j).2

private theorem opposite_layer_separated {V : Type} {R : V → V → Prop}
    {a b : Nat} (p : InducedPath V R a) (q : InducedPath V R b)
    (left right : Bool) (different : left ≠ right)
    (disjoint : ∀ i j, p.vertex i ≠ q.vertex j) :
    ∀ i j, (inLayer p left).vertex i ≠ (inLayer q right).vertex j ∧
      ¬LayerAdj R ((inLayer p left).vertex i) ((inLayer q right).vertex j) := by
  intro i j
  constructor
  · intro equal
    exact different (congrArg Prod.snd equal)
  · simpa [inLayer, LayerAdj, different] using disjoint i j

private theorem opposite_layer_contact {V : Type} {R : V → V → Prop}
    {a b : Nat} (p : InducedPath V R a) (q : InducedPath V R b)
    (left right : Bool) (different : left ≠ right) (compatible : Compatible p q) :
    (∀ i j, (inLayer p left).vertex i ≠ (inLayer q right).vertex j) ∧
    (∀ i j, LayerAdj R ((inLayer p left).vertex i) ((inLayer q right).vertex j) ↔
      i.val = a ∧ j.val = 0) := by
  constructor
  · intro i j equal
    exact different (congrArg Prod.snd equal)
  · intro i j
    simpa [inLayer, LayerAdj, different] using compatible i j

/-- Join five actual induced paths in alternating layers. Consecutive
components share only their prescribed crossing port; nonconsecutive
components are separated according to their layers. No positive-length
hypothesis excludes singleton outer components. -/
def fourCrossings {V : Type} {R : V → V → Prop} {a b c d e : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b)
    (r : InducedPath V R c) (s : InducedPath V R d) (t : InducedPath V R e)
    (pq : Compatible p q) (qr : Compatible q r)
    (rs : Compatible r s) (st : Compatible s t)
    (pr : ∀ i j, p.vertex i ≠ r.vertex j ∧ ¬R (p.vertex i) (r.vertex j))
    (pt : ∀ i j, p.vertex i ≠ t.vertex j ∧ ¬R (p.vertex i) (t.vertex j))
    (rt : ∀ i j, r.vertex i ≠ t.vertex j ∧ ¬R (r.vertex i) (t.vertex j))
    (qs : ∀ i j, q.vertex i ≠ s.vertex j ∧ ¬R (q.vertex i) (s.vertex j))
    (ps : ∀ i j, p.vertex i ≠ s.vertex j)
    (qt : ∀ i j, q.vertex i ≠ t.vertex j) :
    InducedPath (V × Bool) (LayerAdj R) (a + b + c + d + e + 4) := by
  let P := inLayer p false
  let Q := inLayer q true
  let Rpath := inLayer r false
  let S := inLayer s true
  let T := inLayer t false
  have hPQ := opposite_layer_contact p q false true (by decide) pq
  have hQR := opposite_layer_contact q r true false (by decide) qr
  have hRS := opposite_layer_contact r s false true (by decide) rs
  have hST := opposite_layer_contact s t true false (by decide) st
  have hPR := same_layer_separated p r false pr
  have hPT := same_layer_separated p t false pt
  have hRT := same_layer_separated r t false rt
  have hQS := same_layer_separated q s true qs
  have hPS := opposite_layer_separated p s false true (by decide) ps
  have hQT := opposite_layer_separated q t true false (by decide) qt

  let PQ := appendEdge P Q hPQ.1 hPQ.2
  have hPQR := append_last_contact P Q Rpath hPQ.1 hPQ.2 hPR hQR.1 hQR.2
  let PQR := appendEdge PQ Rpath hPQR.1 hPQR.2
  have hPQ_S := append_separated P Q S hPQ.1 hPQ.2 hPS hQS
  have hPQRS := append_last_contact PQ Rpath S hPQR.1 hPQR.2 hPQ_S hRS.1 hRS.2
  let PQRS := appendEdge PQR S hPQRS.1 hPQRS.2
  have hPQ_T := append_separated P Q T hPQ.1 hPQ.2 hPT hQT
  have hPQR_T := append_separated PQ Rpath T hPQR.1 hPQR.2 hPQ_T hRT
  have hPQRST := append_last_contact PQR S T hPQRS.1 hPQRS.2 hPQR_T hST.1 hST.2
  have result := appendEdge PQRS T hPQRST.1 hPQRST.2
  have length_identity : (((a + b + 1) + c + 1) + d + 1) + e + 1 =
      a + b + c + d + e + 4 := by omega
  simpa only [length_identity] using result

#print axioms fourCrossings
end FourCrossings223
