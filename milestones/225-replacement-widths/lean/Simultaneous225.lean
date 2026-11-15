import ReplacementOrdered225

set_option Elab.async false

namespace Simultaneous225
open LayerJoining

/-- Construct the actual candidate path from the packaged local premises. -/
def replaceTwoBlocks {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (q : Fin (n + 1) → V) (a b c d : Nat)
    (conditions : ReplacementConditions225.Conditions p q a b c d) :
    InducedPath V R n where
  vertex := q
  distinct i j equal := by
    apply Fin.ext
    by_cases forward : i.val < j.val
    · exact False.elim ((ReplacementOrdered225.ordered_pair p q a b c d conditions
        i j forward).1 equal)
    · by_cases backward : j.val < i.val
      · exact False.elim ((ReplacementOrdered225.ordered_pair p q a b c d conditions
          j i backward).1 equal.symm)
      · exact ReplacementIndices225.equal_of_nonordered forward backward
  induced i j index_order :=
    (ReplacementOrdered225.ordered_pair p q a b c d conditions i j index_order).2

#print axioms replaceTwoBlocks
end Simultaneous225
