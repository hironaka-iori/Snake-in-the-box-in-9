import HistoryShareCover

namespace Snake9.HistoryShare94
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def signature010 : List Nat := [27,219,35]
def variants010 : List (List Nat) := [[0,1,2,0,3,2,4,5,2,3,1],[0,1,2,0,3,2,4,5,2,3,6]]
theorem share_cover_010 : shareCoverTable signature010 variants010 = true := by
  decide +kernel
#print axioms share_cover_010

def signature011 : List Nat := [29,235,79]
def variants011 : List (List Nat) := [[0,1,2,0,3,2,4,5,6,4,2]]
theorem share_cover_011 : shareCoverTable signature011 variants011 = true := by
  decide +kernel
#print axioms share_cover_011

def signature012 : List Nat := [35,350,180]
def variants012 : List (List Nat) := [[0,1,2,0,3,4,0,2,5,1,0]]
theorem share_cover_012 : shareCoverTable signature012 variants012 = true := by
  decide +kernel
#print axioms share_cover_012

def signature013 : List Nat := [35,351,172]
def variants013 : List (List Nat) := [[0,1,2,0,3,4,0,2,5,0,1],[0,1,2,0,3,4,0,2,5,0,6]]
theorem share_cover_013 : shareCoverTable signature013 variants013 = true := by
  decide +kernel
#print axioms share_cover_013

def signature014 : List Nat := [90,139,350]
def variants014 : List (List Nat) := [[0,1,2,3,0,1,4,0,3,5,2]]
theorem share_cover_014 : shareCoverTable signature014 variants014 = true := by
  decide +kernel
#print axioms share_cover_014

end Snake9.HistoryShare94
