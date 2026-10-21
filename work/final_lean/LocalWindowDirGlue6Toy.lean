import LocalWindowDirGlue6
import LocalWindowDirKeysR4b
import LocalWindowDirKeysR4
import LocalWindowDirKeys6Toy

/-!
# Toy instance of the mixed-key glue

The five keys of the toy six-centre automaton (`dirKeys6Toy`) are drawn from three sources:
key 0 (two centres) from the 237 set `dirKeysR4b`, key 1 (four centres) from the 236 set
`dirKeysR4`, and the three six-centre keys from a list of new certificates `newKeys6Toy`.
So the toy premise `AllRefuted6Toy` follows from the 237 and 236 premises and the new
certificates; `pickOK` (index witnesses) and `mergeOK` (source tags) are each checked by
one kernel evaluation.
-/

namespace Snake9.LocalWindow

/-- The toy keys that no earlier set certifies. -/
def newKeys6Toy : List DirKey := [
  ([0, 1, 2, 0, 3, 1, 0], [1, 5, 6, 1, 5, 2]),
  ([0, 1, 2, 3, 0, 1, 4], [2, 2, 6, 2, 2, 3]),
  ([0, 1, 2, 3, 0, 1, 4], [2, 3, 6, 2, 2, 3])]

/-- Witnesses `(source, index)` for the keys of `dirKeys6Toy`, in order. -/
def pick6Toy : List (Nat × Nat) := [(0, 0), (1, 47), (2, 0), (2, 1), (2, 2)]

theorem pick6Toy_ok : pickOK [dirKeysR4b, dirKeysR4, newKeys6Toy] dirKeys6Toy pick6Toy = true := by
  decide +kernel

theorem allRefuted6Toy_of_parts (h237 : AllRefuted237) (h236 : AllRefuted236)
    (hnew : AllRefutedList newKeys6Toy) : AllRefuted6Toy :=
  allRefuted_of_pick3 h237 h236 hnew pick6Toy_ok

/-- The same by the merge check: one source tag per key. -/
theorem merge6Toy_ok : mergeOK [dirKeysR4b, dirKeysR4, newKeys6Toy] dirKeys6Toy [0, 1, 2, 2, 2] = true := by
  decide +kernel

theorem allRefuted6Toy_of_parts' (h237 : AllRefuted237) (h236 : AllRefuted236)
    (hnew : AllRefutedList newKeys6Toy) : AllRefuted6Toy :=
  allRefuted_of_merge3 h237 h236 hnew merge6Toy_ok

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefuted_of_pick
#print axioms Snake9.LocalWindow.allRefuted_of_pick3
#print axioms Snake9.LocalWindow.allRefuted6Toy_of_parts
#print axioms Snake9.LocalWindow.allRefuted_of_merge3
#print axioms Snake9.LocalWindow.allRefuted6Toy_of_parts'
