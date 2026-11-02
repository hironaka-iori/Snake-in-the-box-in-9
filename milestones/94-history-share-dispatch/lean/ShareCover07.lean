import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature035 : List Nat := [350,182,78]
def variants035 : List (List Nat) := [[0,1,2,3,4,2,1,5,0,4,6]]
theorem share_cover_035 : shareCoverTable signature035 variants035 = true := by
  decide +kernel
#print axioms share_cover_035

def signature036 : List Nat := [351,171,35]
def variants036 : List (List Nat) := [[0,1,2,3,4,2,1,5,2,4,0],[0,1,2,3,4,2,1,5,2,4,6]]
theorem share_cover_036 : shareCoverTable signature036 variants036 = true := by
  decide +kernel
#print axioms share_cover_036

def signature037 : List Nat := [351,172,39]
def variants037 : List (List Nat) := [[0,1,2,3,4,2,1,5,2,0,5],[0,1,2,3,4,2,1,5,2,6,5]]
theorem share_cover_037 : shareCoverTable signature037 variants037 = true := by
  decide +kernel
#print axioms share_cover_037

def signature038 : List Nat := [353,177,55]
def variants038 : List (List Nat) := [[0,1,2,3,4,2,1,5,4,2,0],[0,1,2,3,4,2,1,5,4,2,6]]
theorem share_cover_038 : shareCoverTable signature038 variants038 = true := by
  decide +kernel
#print axioms share_cover_038

def signature039 : List Nat := [354,181,73]
def variants039 : List (List Nat) := [[0,1,2,3,4,2,1,5,6,3,0],[0,1,2,3,4,2,1,5,6,3,7]]
theorem share_cover_039 : shareCoverTable signature039 variants039 = true := by
  decide +kernel
#print axioms share_cover_039

end Snake9.HistoryShare94
