import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature030 : List Nat := [264,395,460]
def variants030 : List (List Nat) := [[0,1,2,3,4,0,5,1,0,4,2]]
theorem share_cover_030 : shareCoverTable signature030 variants030 = true := by
  decide +kernel
#print axioms share_cover_030

def signature031 : List Nat := [264,395,462]
def variants031 : List (List Nat) := [[0,1,2,3,4,0,5,1,0,4,6]]
theorem share_cover_031 : shareCoverTable signature031 variants031 = true := by
  decide +kernel
#print axioms share_cover_031

def signature032 : List Nat := [281,460,354]
def variants032 : List (List Nat) := [[0,1,2,3,4,0,5,4,3,1,6]]
theorem share_cover_032 : shareCoverTable signature032 variants032 = true := by
  decide +kernel
#print axioms share_cover_032

def signature033 : List Nat := [302,90,139]
def variants033 : List (List Nat) := [[0,1,2,3,4,1,2,5,1,4,0],[0,1,2,3,4,1,2,5,1,4,6]]
theorem share_cover_033 : shareCoverTable signature033 variants033 = true := by
  decide +kernel
#print axioms share_cover_033

def signature034 : List Nat := [305,99,147]
def variants034 : List (List Nat) := [[0,1,2,3,4,1,2,5,6,2,1]]
theorem share_cover_034 : shareCoverTable signature034 variants034 = true := by
  decide +kernel
#print axioms share_cover_034

end Snake9.HistoryShare94
