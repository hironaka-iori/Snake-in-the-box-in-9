import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature040 : List Nat := [354,182,78]
def variants040 : List (List Nat) := [[0,1,2,3,4,2,1,5,6,4,0],[0,1,2,3,4,2,1,5,6,4,7]]
theorem share_cover_040 : shareCoverTable signature040 variants040 = true := by
  decide +kernel
#print axioms share_cover_040

def signature041 : List Nat := [395,460,354]
def variants041 : List (List Nat) := [[0,1,2,3,4,5,0,4,3,1,6]]
theorem share_cover_041 : shareCoverTable signature041 variants041 = true := by
  decide +kernel
#print axioms share_cover_041

def signature042 : List Nat := [426,281,460]
def variants042 : List (List Nat) := [[0,1,2,3,4,5,1,6,5,4,2]]
theorem share_cover_042 : shareCoverTable signature042 variants042 = true := by
  decide +kernel
#print axioms share_cover_042

def signature043 : List Nat := [426,281,462]
def variants043 : List (List Nat) := [[0,1,2,3,4,5,1,6,5,4,0],[0,1,2,3,4,5,1,6,5,4,7]]
theorem share_cover_043 : shareCoverTable signature043 variants043 = true := by
  decide +kernel
#print axioms share_cover_043

def signature044 : List Nat := [440,302,90]
def variants044 : List (List Nat) := [[0,1,2,3,4,5,2,3,6,2,5]]
theorem share_cover_044 : shareCoverTable signature044 variants044 = true := by
  decide +kernel
#print axioms share_cover_044

end Snake9.HistoryShare94
