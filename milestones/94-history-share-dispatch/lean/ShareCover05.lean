import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature025 : List Nat := [177,55,305]
def variants025 : List (List Nat) := [[0,1,2,3,1,0,4,3,1,5,6]]
theorem share_cover_025 : shareCoverTable signature025 variants025 = true := by
  decide +kernel
#print axioms share_cover_025

def signature026 : List Nat := [215,79,462]
def variants026 : List (List Nat) := [[0,1,2,3,1,4,5,0,4,1,6]]
theorem share_cover_026 : shareCoverTable signature026 variants026 = true := by
  decide +kernel
#print axioms share_cover_026

def signature027 : List Nat := [219,34,348]
def variants027 : List (List Nat) := [[0,1,2,3,1,4,5,1,3,2,1]]
theorem share_cover_027 : shareCoverTable signature027 variants027 = true := by
  decide +kernel
#print axioms share_cover_027

def signature028 : List Nat := [219,35,351]
def variants028 : List (List Nat) := [[0,1,2,3,1,4,5,1,3,0,1],[0,1,2,3,1,4,5,1,3,6,1]]
theorem share_cover_028 : shareCoverTable signature028 variants028 = true := by
  decide +kernel
#print axioms share_cover_028

def signature029 : List Nat := [235,79,462]
def variants029 : List (List Nat) := [[0,1,2,3,1,4,5,6,4,1,0],[0,1,2,3,1,4,5,6,4,1,7]]
theorem share_cover_029 : shareCoverTable signature029 variants029 = true := by
  decide +kernel
#print axioms share_cover_029

end Snake9.HistoryShare94
