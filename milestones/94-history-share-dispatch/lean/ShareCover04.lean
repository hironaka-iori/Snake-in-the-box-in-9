import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature020 : List Nat := [147,460,350]
def variants020 : List (List Nat) := [[0,1,2,3,0,4,5,0,3,1,2]]
theorem share_cover_020 : shareCoverTable signature020 variants020 = true := by
  decide +kernel
#print axioms share_cover_020

def signature021 : List Nat := [147,460,351]
def variants021 : List (List Nat) := [[0,1,2,3,0,4,5,0,3,1,0]]
theorem share_cover_021 : shareCoverTable signature021 variants021 = true := by
  decide +kernel
#print axioms share_cover_021

def signature022 : List Nat := [147,460,352]
def variants022 : List (List Nat) := [[0,1,2,3,0,4,5,0,3,1,4]]
theorem share_cover_022 : shareCoverTable signature022 variants022 = true := by
  decide +kernel
#print axioms share_cover_022

def signature023 : List Nat := [147,460,354]
def variants023 : List (List Nat) := [[0,1,2,3,0,4,5,0,3,1,6]]
theorem share_cover_023 : shareCoverTable signature023 variants023 = true := by
  decide +kernel
#print axioms share_cover_023

def signature024 : List Nat := [175,50,264]
def variants024 : List (List Nat) := [[0,1,2,3,1,0,4,2,5,3,2]]
theorem share_cover_024 : shareCoverTable signature024 variants024 = true := by
  decide +kernel
#print axioms share_cover_024

end Snake9.HistoryShare94
