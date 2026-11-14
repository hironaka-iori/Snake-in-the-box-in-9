import Std
namespace WholeSnakeExample202

def original : Array Nat := #[0,1,3,7,15,14,10,26,18,22,20,28,29,25]
def transformed : Array Nat := #[0,1,3,7,15,14,10,26,18,22,20,21,29,25]

def change (x : Nat) : Nat := if x=21 then 28 else if x=28 then 21 else x

def Adj (x y : Nat) : Prop :=
  let d := Nat.xor x y
  d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16
instance (x y : Nat) : Decidable (Adj x y) := inferInstanceAs (Decidable (_ ∨ _))

def distance (x y : Nat) : Nat :=
  (List.range 5).foldl (fun n c => n + if (Nat.xor x y).testBit c then 1 else 0) 0

theorem bothSnakes : ∀ i j : Fin 14,
    (original[i.val]! = original[j.val]! ↔ i=j) ∧
    (transformed[i.val]! = transformed[j.val]! ↔ i=j) ∧
    (Adj original[i.val]! original[j.val]! ↔ i.val+1=j.val ∨ j.val+1=i.val) ∧
    (Adj transformed[i.val]! transformed[j.val]! ↔ i.val+1=j.val ∨ j.val+1=i.val) := by
  decide +kernel

theorem wholeImage : ∀ i : Fin 14, change original[i.val]! = transformed[i.val]! := by
  decide +kernel

theorem distanceObstruction :
    ¬ ((∀ i j : Fin 14, distance original[i.val]! original[j.val]! = distance transformed[i.val]! transformed[j.val]!) ∨
       (∀ i j : Fin 14, distance original[i.val]! original[j.val]! = distance transformed[13-i.val]! transformed[13-j.val]!)) := by
  decide +kernel

#print axioms bothSnakes
#print axioms wholeImage
#print axioms distanceObstruction
end WholeSnakeExample202
