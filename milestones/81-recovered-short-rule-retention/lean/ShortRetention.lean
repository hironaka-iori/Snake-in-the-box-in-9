import CapCatalogue
import SumCatalogue

namespace Snake9.ShortRules81
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.GraphWalk78

def shortRules : List (List Nat × CountTest) := capRules ++ sumRules

theorem short_catalogue : ∀ rule ∈ shortRules, rawSafe rule.1 rule.2 ∧
    smallCaps rule.2 ∧ internalPositions rule.2 rule.1.length := by
  intro rule h
  rcases List.mem_append.mp h with h | h
  · exact cap_catalogue rule h
  · exact sum_catalogue rule h

theorem short_rules_length : shortRules.length = 40 := by decide

theorem all_short_rules_retained {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    ∀ rule ∈ shortRules, ∀ offset : Nat, ∀ reverse : Bool,
      offset+rule.1.length ≤ 9 →
      (∀ j ∈ rule.2.positions, 3 ≤ offset+orientedPosition rule.1.length reverse j ∧
        offset+orientedPosition rule.1.length reverse j ≤ 8) →
      canon (if reverse then
        (((canon (dsOf p r 9)).drop offset).take rule.1.length).reverse
        else ((canon (dsOf p r 9)).drop offset).take rule.1.length) = rule.1 →
      ¬ encodedBad rule.2 (fun j => digit (sixCode p r)
        (offset+orientedPosition rule.1.length reverse j-3)) := by
  intro rule h offset reverse ho hpos hshape
  obtain ⟨hsafe,hsmall,hint⟩ := short_catalogue rule h
  exact encoded_guard_retention rule.1 rule.2 hsafe hsmall hint p r offset reverse hr ho hpos hshape

#print axioms short_catalogue
#print axioms short_rules_length
#print axioms all_short_rules_retained
end Snake9.ShortRules81
