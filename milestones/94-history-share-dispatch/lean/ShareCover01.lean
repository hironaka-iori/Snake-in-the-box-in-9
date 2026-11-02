import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature005 : List Nat := [258,350,180]
def variants005 : List (List Nat) := [[0,1,2,3,4,0,3,2,5,1,3]]
theorem share_cover_005 : shareCoverTable signature005 variants005 = true := by
  decide +kernel
#print axioms share_cover_005

def signature006 : List Nat := [258,354,180]
def variants006 : List (List Nat) := [[0,1,2,3,4,0,3,2,5,6,3]]
theorem share_cover_006 : shareCoverTable signature006 variants006 = true := by
  decide +kernel
#print axioms share_cover_006

def signature007 : List Nat := [350,181,73]
def variants007 : List (List Nat) := [[0,1,2,3,4,2,1,5,0,3,6]]
theorem share_cover_007 : shareCoverTable signature007 variants007 = true := by
  decide +kernel
#print axioms share_cover_007

def signature008 : List Nat := [26,215,79]
def variants008 : List (List Nat) := [[0,1,2,0,3,2,4,5,1,4,2]]
theorem share_cover_008 : shareCoverTable signature008 variants008 = true := by
  decide +kernel
#print axioms share_cover_008

def signature009 : List Nat := [27,219,34]
def variants009 : List (List Nat) := [[0,1,2,0,3,2,4,5,2,3,0]]
theorem share_cover_009 : shareCoverTable signature009 variants009 = true := by
  decide +kernel
#print axioms share_cover_009

end Snake9.HistoryShare94
