import IntervalGuards

namespace Snake9.History84
open Snake9.WindowAutomaton Snake9.Direction77
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def realizes (sig cs : List Nat) : Bool :=
  (canon (cs.take 9) == extensions.getD (sig.getD 0 0) []) &&
  (canon ((cs.drop 1).take 9) == extensions.getD (sig.getD 1 0) []) &&
  (canon ((cs.drop 2).take 9) == extensions.getD (sig.getD 2 0) [])

def realizationTable (sig expected : List Nat) : Bool :=
  allBelow 9 fun a => allBelow 9 fun b =>
    let cs := extensions.getD (sig.getD 0 0) [] ++ [a,b]
    !isRGS cs 0 || !inducedPattern cs || !realizes sig cs || (cs == expected)

def signature0 : List Nat := [139,353,177]
def word0 : List Nat := [0,1,2,3,0,4,3,2,5,4,3]
theorem realization_table_0 : realizationTable signature0 word0 = true := by
  decide +kernel
#print axioms realization_table_0

def signature1 : List Nat := [460,350,180]
def word1 : List Nat := [0,1,2,3,4,5,3,2,0,1,3]
theorem realization_table_1 : realizationTable signature1 word1 = true := by
  decide +kernel
#print axioms realization_table_1

def signature2 : List Nat := [460,353,177]
def word2 : List Nat := [0,1,2,3,4,5,3,2,0,5,3]
theorem realization_table_2 : realizationTable signature2 word2 = true := by
  decide +kernel
#print axioms realization_table_2

end Snake9.History84
