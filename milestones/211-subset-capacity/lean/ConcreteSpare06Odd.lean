import ConcreteSpare06

namespace ConcreteSpare06Odd
open ConcreteSpare06

def oddClique : List Nat := multi 1 ++ single 1 0 ++ single 1 1
def oddOutside : List Nat := single 1 2 ++ single 1 3

theorem odd_counts : counts 1 = [9,8,9,6,7] := by
  decide +kernel

theorem odd_partition :
    oddClique.length = 26 ∧ oddOutside.length = 13 ∧
    (oddClique ++ oddOutside).Nodup ∧
    (oddClique ++ oddOutside).all (fun g => decide (g < rawVisits.length ∧ g % 2 = 1)) = true ∧
    (List.range rawVisits.length).all (fun g => decide (g % 2 = 1 → g ∈ oddClique ++ oddOutside)) = true := by
  decide +kernel

#print axioms odd_counts
#print axioms odd_partition
end ConcreteSpare06Odd
