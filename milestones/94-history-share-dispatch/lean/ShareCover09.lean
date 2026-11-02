import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature045 : List Nat := [460,350,183]
def variants045 : List (List Nat) := [[0,1,2,3,4,5,3,2,0,1,6]]
theorem share_cover_045 : shareCoverTable signature045 variants045 = true := by
  decide +kernel
#print axioms share_cover_045

def signature046 : List Nat := [460,352,175]
def variants046 : List (List Nat) := [[0,1,2,3,4,5,3,2,0,4,6]]
theorem share_cover_046 : shareCoverTable signature046 variants046 = true := by
  decide +kernel
#print axioms share_cover_046

def signature047 : List Nat := [462,350,180]
def variants047 : List (List Nat) := [[0,1,2,3,4,5,3,2,6,1,3]]
theorem share_cover_047 : shareCoverTable signature047 variants047 = true := by
  decide +kernel
#print axioms share_cover_047

def signature048 : List Nat := [462,350,181]
def variants048 : List (List Nat) := [[0,1,2,3,4,5,3,2,6,1,4]]
theorem share_cover_048 : shareCoverTable signature048 variants048 = true := by
  decide +kernel
#print axioms share_cover_048

def signature049 : List Nat := [462,350,182]
def variants049 : List (List Nat) := [[0,1,2,3,4,5,3,2,6,1,5]]
theorem share_cover_049 : shareCoverTable signature049 variants049 = true := by
  decide +kernel
#print axioms share_cover_049

end Snake9.HistoryShare94
