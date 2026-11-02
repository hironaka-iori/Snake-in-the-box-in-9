import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature015 : List Nat := [90,139,354]
def variants015 : List (List Nat) := [[0,1,2,3,0,1,4,0,3,5,6]]
theorem share_cover_015 : shareCoverTable signature015 variants015 = true := by
  decide +kernel
#print axioms share_cover_015

def signature016 : List Nat := [99,147,460]
def variants016 : List (List Nat) := [[0,1,2,3,0,1,4,5,1,0,2]]
theorem share_cover_016 : shareCoverTable signature016 variants016 = true := by
  decide +kernel
#print axioms share_cover_016

def signature017 : List Nat := [99,147,461]
def variants017 : List (List Nat) := [[0,1,2,3,0,1,4,5,1,0,3]]
theorem share_cover_017 : shareCoverTable signature017 variants017 = true := by
  decide +kernel
#print axioms share_cover_017

def signature018 : List Nat := [99,147,462]
def variants018 : List (List Nat) := [[0,1,2,3,0,1,4,5,1,0,6]]
theorem share_cover_018 : shareCoverTable signature018 variants018 = true := by
  decide +kernel
#print axioms share_cover_018

def signature019 : List Nat := [139,350,179]
def variants019 : List (List Nat) := [[0,1,2,3,0,4,3,2,5,1,2]]
theorem share_cover_019 : shareCoverTable signature019 variants019 = true := by
  decide +kernel
#print axioms share_cover_019

end Snake9.HistoryShare94
