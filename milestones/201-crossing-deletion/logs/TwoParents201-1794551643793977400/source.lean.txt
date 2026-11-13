import CrossingDeletion201
namespace TwoParents201
open CrossingDeletion201

theorem twoParentAccounting (a b : Bool) (xs ys : List Bool) (A H K L : Nat)
    (vertices : L+1=selected (a::xs)+selected (b::ys)+A)
    (pathEdges : railEdges (a::xs)+railEdges (b::ys)+H+K=L) :
    K + (bit (!a)+bit (!(lastBit a xs))+bit (!b)+bit (!(lastBit b ys))) +
      (railEdges ((a::xs).map Bool.not)+railEdges ((b::ys).map Bool.not)) + H =
      1+deleted (a::xs)+deleted (b::ys)+A ∧
    L+K+(bit (!a)+bit (!(lastBit a xs))+bit (!b)+bit (!(lastBit b ys)))+
      (railEdges ((a::xs).map Bool.not)+railEdges ((b::ys).map Bool.not))+H =
      (a::xs).length+(b::ys).length+2*A := by
  have pa := vertexPartition (a::xs)
  have pb := vertexPartition (b::ys)
  have ea := railAccounting a xs
  have eb := railAccounting b ys
  simp only [List.length_cons] at *
  omega

theorem twoParentLengthBound (a b : Bool) (xs ys : List Bool)
    (M A H K L : Nat) (hx : xs.length ≤ M) (hy : ys.length ≤ M)
    (vertices : L+1=selected (a::xs)+selected (b::ys)+A)
    (pathEdges : railEdges (a::xs)+railEdges (b::ys)+H+K=L) :
    L+K ≤ 2*M+2+2*A := by
  have h := (twoParentAccounting a b xs ys A H K L vertices pathEdges).2
  simp only [List.length_cons] at h
  omega

#print axioms twoParentAccounting
#print axioms twoParentLengthBound
end TwoParents201
