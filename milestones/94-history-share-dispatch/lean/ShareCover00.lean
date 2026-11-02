import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature000 : List Nat := [54,300,99]
def variants000 : List (List Nat) := [[0,1,2,0,3,4,2,0,1,5,0]]
theorem share_cover_000 : shareCoverTable signature000 variants000 = true := by
  decide +kernel
#print axioms share_cover_000

def signature001 : List Nat := [66,438,302]
def variants001 : List (List Nat) := [[0,1,2,0,3,4,5,0,3,1,0]]
theorem share_cover_001 : shareCoverTable signature001 variants001 = true := by
  decide +kernel
#print axioms share_cover_001

def signature002 : List Nat := [66,439,299]
def variants002 : List (List Nat) := [[0,1,2,0,3,4,5,0,3,2,0]]
theorem share_cover_002 : shareCoverTable signature002 variants002 = true := by
  decide +kernel
#print axioms share_cover_002

def signature003 : List Nat := [177,54,300]
def variants003 : List (List Nat) := [[0,1,2,3,1,0,4,3,1,2,5]]
theorem share_cover_003 : shareCoverTable signature003 variants003 = true := by
  decide +kernel
#print axioms share_cover_003

def signature004 : List Nat := [177,55,301]
def variants004 : List (List Nat) := [[0,1,2,3,1,0,4,3,1,5,2]]
theorem share_cover_004 : shareCoverTable signature004 variants004 = true := by
  decide +kernel
#print axioms share_cover_004

end Snake9.HistoryShare94
