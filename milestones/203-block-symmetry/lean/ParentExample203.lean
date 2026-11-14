import Std
namespace ParentExample203
set_option maxRecDepth 100000
def original : Array Nat := #[0,1,3,7,6,14,12,13,29,25,27,26,18,50,51,49,53,37,36,100,68,69,85,81,80,88,72,73,75,79,95,94,86,118,119,103,99,98,106,122,123,121,125,124,60,56,40,41,43,47,63]
def transformed : Array Nat := #[0,1,3,7,6,14,12,13,29,25,27,26,18,50,51,49,53,37,36,100,68,69,85,81,80,88,72,73,75,79,95,94,86,118,119,103,99,98,106,122,123,121,125,124,60,62,63,47,43,41,40]
def blockMap (x : Nat) : Nat :=
  (if x.testBit 4 then 0 else 1)+(if x.testBit 2 then 0 else 2)+
  (if x.testBit 1 then 0 else 4)+(if x.testBit 3 then 8 else 0)+
  (if x.testBit 0 then 0 else 16)+(if x.testBit 5 then 32 else 0)+
  (if x.testBit 6 then 64 else 0)
def change (x : Nat) : Nat := if x &&& 104 = 40 then blockMap x else x
def Adj (x y : Nat) : Prop :=
  let d := Nat.xor x y
  d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32 ∨ d=64
instance (x y : Nat) : Decidable (Adj x y) := inferInstanceAs (Decidable (_ ∨ _))
def distance (x y : Nat) : Nat :=
  (List.range 7).foldl (fun n c => n + if (Nat.xor x y).testBit c then 1 else 0) 0
theorem completeSnakes : ∀ i j : Fin 51,
    original[i.val]! < 128 ∧ transformed[i.val]! < 128 ∧
    (original[i.val]! = original[j.val]! ↔ i=j) ∧
    (transformed[i.val]! = transformed[j.val]! ↔ i=j) ∧
    (Adj original[i.val]! original[j.val]! ↔ i.val+1=j.val ∨ j.val+1=i.val) ∧
    (Adj transformed[i.val]! transformed[j.val]! ↔ i.val+1=j.val ∨ j.val+1=i.val) := by
  decide +kernel
theorem wholeImage : ∀ i : Fin 51, change original[i.val]! = transformed[i.val]! := by
  decide +kernel
theorem endpointsDifferent : distance original[0]! original[50]! =6 ∧
    distance transformed[0]! transformed[50]! =2 := by decide +kernel
#print axioms completeSnakes
#print axioms wholeImage
#print axioms endpointsDifferent
end ParentExample203
