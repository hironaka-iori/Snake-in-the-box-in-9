import LayerJoining
import AttachmentBalance191
namespace CrossingDeletion201
open LayerJoining Replacement191

def bit (b : Bool) : Nat := if b then 1 else 0
def selected (xs : List Bool) : Nat := count xs id
def deleted (xs : List Bool) : Nat := count xs (fun b => !b)
def railEdges : List Bool → Nat
  | [] => 0
  | [_] => 0
  | a::b::xs => bit (a && b) + railEdges (b::xs)
def lastBit (a : Bool) : List Bool → Bool
  | [] => a
  | b::xs => lastBit b xs

theorem vertexPartition (xs : List Bool) : selected xs + deleted xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change bit a + selected xs + (bit (!a) + deleted xs) = xs.length+1
    have hv : bit a + bit (!a) = 1 := by cases a <;> rfl
    omega

theorem oneRail : ∀ a b : Bool,
    bit (a && b) + 2*bit (!a) + bit (!b) =
      1 + bit (!a) + bit (!a && !b) := by decide +kernel

theorem railAccounting (a : Bool) (xs : List Bool) :
    railEdges (a::xs) + 2*deleted (a::xs) =
      xs.length + bit (!a) + bit (!(lastBit a xs)) +
        railEdges ((a::xs).map Bool.not) := by
  induction xs generalizing a with
  | nil => cases a <;> rfl
  | cons b xs ih =>
    have ht := ih b
    have hv := oneRail a b
    change bit (a && b) + railEdges (b::xs) +
      2*(bit (!a) + deleted (b::xs)) =
      xs.length+1 + bit (!a) + bit (!(lastBit b xs)) +
        (bit (!a && !b) + railEdges ((b::xs).map Bool.not))
    omega

theorem oneOverlap : ∀ a b c d : Bool,
    bit (a && b) ≤ bit (c && d) + bit (a && !c) + bit (b && !d) := by
  decide +kernel

theorem overlapSurvives {V : Type} (xs : List V) (p q r s : V → Bool) :
    count xs (fun v => p v && q v) ≤ count xs (fun v => r v && s v) +
      count xs (fun v => p v && !r v) + count xs (fun v => q v && !s v) := by
  induction xs with
  | nil => simp [count]
  | cons v vs ih =>
    have hv := oneOverlap (p v) (q v) (r v) (s v)
    change bit (p v && q v) + count vs (fun v => p v && q v) ≤
      (bit (r v && s v) + count vs (fun v => r v && s v)) +
      (bit (p v && !r v) + count vs (fun v => p v && !r v)) +
      (bit (q v && !s v) + count vs (fun v => q v && !s v))
    omega

theorem crossingIdentity (N D A B E H K L retainedEdges : Nat)
    (parentRails : retainedEdges+2*D+2=N+B+E)
    (vertices : L+1+D=N+A)
    (pathEdges : retainedEdges+H+K=L) :
    K+B+E+H=1+D+A ∧ L+K+B+E+H=N+2*A := by omega

theorem dimensionalBound (a p q A B E H K L : Nat)
    (hp : p ≤ a) (hq : q ≤ a)
    (identity : L+K+B+E+H=p+q+2+2*A) :
    L+K ≤ 2*a+2+2*A := by omega

theorem deletion98 (p q D B E H K : Nat)
    (hp : p ≤ 50) (hq : q ≤ 50)
    (vertices : 99+D=p+q+2)
    (identity : 98+K+B+E+H=p+q+2) (crossings : 4 ≤ K) :
    p=50 ∧ q=50 ∧ D=3 ∧ K=4 ∧ B=0 ∧ E=0 ∧ H=0 := by omega

theorem deletion196 (p q D B E H K : Nat)
    (hp : p ≤ 98) (hq : q ≤ 98)
    (vertices : 197+D=p+q+2)
    (identity : 196+K+B+E+H=p+q+2) : D ≤ 1 ∧ K ≤ 2 := by omega

theorem oneAddition196 (p q D B E H K : Nat)
    (hp : p ≤ 98) (hq : q ≤ 98)
    (vertices : 197+D=p+q+3)
    (identity : 196+K+B+E+H=p+q+4) (crossings : 4 ≤ K) :
    p=98 ∧ q=98 ∧ D=2 ∧ K=4 ∧ B=0 ∧ E=0 ∧ H=0 := by omega

#print axioms vertexPartition
#print axioms oneRail
#print axioms railAccounting
#print axioms oneOverlap
#print axioms overlapSurvives
#print axioms crossingIdentity
#print axioms dimensionalBound
#print axioms deletion98
#print axioms deletion196
#print axioms oneAddition196
end CrossingDeletion201
