import AttachmentBalance191
namespace CutObstruction201
open Replacement191

def vertices : List Nat :=
  [0,1,3,7,15,13,12,28,30,62,46,38,36,52,116,124,108,109,111,103,
   119,55,183,167,175,173,172,188,184,56,40,41,43,59,187,155,153,137,
   136,138,202,194,192,193,209,211,243,227,235,233,249,253,245,229,
   228,230,238,254,250,122,106,98,96,97,113,49,177,161,160,162,178,
   50,18,82,80,88,72,73,75,91,95,223,207,205,204,220,212,214,150,
   134,132,133,149,21,85,69,68,70,78]

def crossings (c : Nat) : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a::b::xs => (if a.testBit c != b.testBit c then 1 else 0) + crossings c (b::xs)

def faceSize (c : Nat) (b : Bool) : Nat :=
  count vertices (fun x => x.testBit c == b)

theorem allCuts : ∀ c : Fin 8,
    5 ≤ crossings c.val vertices ∨ 51 < faceSize c.val false ∨ 51 < faceSize c.val true := by
  decide +kernel

theorem fourCrossingCut : crossings 5 vertices=4 ∧
    faceSize 5 false=47 ∧ faceSize 5 true=52 ∧ vertices.length=99 := by
  decide +kernel

theorem noTwoParents (c : Fin 8)
    (lengthBound : 98+crossings c.val vertices ≤ 102)
    (face0 : faceSize c.val false ≤ 51) (face1 : faceSize c.val true ≤ 51) : False := by
  rcases allCuts c with h | h | h <;> omega

#print axioms allCuts
#print axioms fourCrossingCut
#print axioms noTwoParents
end CutObstruction201
