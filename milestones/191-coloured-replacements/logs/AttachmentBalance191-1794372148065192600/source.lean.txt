import Std
namespace Replacement191

def count {V : Type} (xs : List V) (p : V → Bool) : Nat :=
  match xs with
  | [] => 0
  | v::vs => (if p v then 1 else 0) + count vs p

theorem onePartition (a b : Bool) :
    (if a then 1 else 0 : Nat) =
      (if a && b then 1 else 0) + (if a && !b then 1 else 0) := by
  cases a <;> cases b <;> rfl

theorem countPartition {V : Type} (xs : List V) (p q : V → Bool) :
    count xs p = count xs (fun v => p v && q v) +
      count xs (fun v => p v && !q v) := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    simp only [count]
    have hv := onePartition (p v) (q v)
    omega

theorem intersectionSymmetric {V : Type} (xs : List V) (p q : V → Bool) :
    count xs (fun v => p v && q v) = count xs (fun v => q v && p v) := by
  induction xs with
  | nil => rfl
  | cons v vs ih => simp only [count, Bool.and_comm, ih]

theorem retainedVertexBalance {V : Type} (neighbours : List V) (p q : V → Bool)
    (sameDegree : count neighbours p = count neighbours q) :
    count neighbours (fun v => p v && !q v) =
      count neighbours (fun v => q v && !p v) := by
  have hp := countPartition neighbours p q
  have hq := countPartition neighbours q p
  have hc := intersectionSymmetric neighbours p q
  omega

theorem gainedColour {V : Type} (vertices : List V) (p q colour : V → Bool)
    (growth : count vertices (fun v => q v && colour v) =
      count vertices (fun v => p v && colour v) + 1) :
    count vertices (fun v => (q v && colour v) && !(p v && colour v)) =
      count vertices (fun v => (p v && colour v) && !(q v && colour v)) + 1 := by
  have hp := countPartition vertices (fun v => p v && colour v) (fun v => q v && colour v)
  have hq := countPartition vertices (fun v => q v && colour v) (fun v => p v && colour v)
  have hc := intersectionSymmetric vertices (fun v => p v && colour v) (fun v => q v && colour v)
  omega

#print axioms countPartition
#print axioms retainedVertexBalance
#print axioms gainedColour
end Replacement191
