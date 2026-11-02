import CompletedPotential99
import ConditionalPotential99

set_option autoImplicit false

namespace Snake9.PotentialBlocks102
open Snake9.Potential99 Snake9.Balanced89

theorem block_div_mod (block offset : Nat) (hoff : offset < 7776) :
    (7776*block+offset)/7776 = block ∧
    (7776*block+offset)%7776 = offset := by omega

theorem completed_block (block offset : Nat) (hoff : offset < 7776) :
    Completed.potential (7776*block+offset) =
      min 551 (value (lookup Completed.roots block (.leaf 0)) offset) := by
  have h := block_div_mod block offset hoff
  simp only [Completed.potential, h.1, h.2]

theorem conditional_block (block offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (7776*block+offset) =
      min 602 (value (lookup Conditional.roots block (.leaf 0)) offset) := by
  have h := block_div_mod block offset hoff
  simp only [Conditional.potential, h.1, h.2]

#print axioms block_div_mod
#print axioms completed_block
#print axioms conditional_block
end Snake9.PotentialBlocks102
