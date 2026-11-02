import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature050 : List Nat := [462,350,183]
def variants050 : List (List Nat) := [[0,1,2,3,4,5,3,2,6,1,0],[0,1,2,3,4,5,3,2,6,1,7]]
theorem share_cover_050 : shareCoverTable signature050 variants050 = true := by
  decide +kernel
#print axioms share_cover_050

def signature051 : List Nat := [462,353,177]
def variants051 : List (List Nat) := [[0,1,2,3,4,5,3,2,6,5,3]]
theorem share_cover_051 : shareCoverTable signature051 variants051 = true := by
  decide +kernel
#print axioms share_cover_051

def signature052 : List Nat := [479,395,460]
def variants052 : List (List Nat) := [[0,1,2,3,4,5,6,1,5,4,2]]
theorem share_cover_052 : shareCoverTable signature052 variants052 = true := by
  decide +kernel
#print axioms share_cover_052

def signature053 : List Nat := [479,395,462]
def variants053 : List (List Nat) := [[0,1,2,3,4,5,6,1,5,4,0],[0,1,2,3,4,5,6,1,5,4,7]]
theorem share_cover_053 : shareCoverTable signature053 variants053 = true := by
  decide +kernel
#print axioms share_cover_053

def signature054 : List Nat := [496,460,354]
def variants054 : List (List Nat) := [[0,1,2,3,4,5,6,4,3,1,0],[0,1,2,3,4,5,6,4,3,1,7]]
theorem share_cover_054 : shareCoverTable signature054 variants054 = true := by
  decide +kernel
#print axioms share_cover_054

end Snake9.HistoryShare94
