import ExtendedShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G012
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 20, 52]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 3, 5]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 16, 17, 19, 21, 22, 23, 24, 29, 30, 33, 35, 38, 39, 44, 46, 60, 65, 67, 70, 71, 76, 78, 84, 92, 129, 131, 134, 135, 140, 142, 148, 156, 257, 259, 262, 263, 268, 270, 276, 284]
def C : List Nat := [6, 14, 12, 28, 20]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 14 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    14 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G012


namespace G013
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 60, 61]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 5, 0]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 22, 23, 24, 29, 30, 33, 35, 38, 39, 44, 46, 52, 56, 62, 65, 67, 70, 71, 76, 78, 92, 124, 129, 131, 134, 135, 140, 142, 156, 188, 257, 259, 262, 263, 268, 270, 284, 316]
def C : List Nat := [6, 14, 12, 28, 60]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G013


namespace G014
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 60, 62]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 5, 1]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 22, 23, 24, 29, 30, 33, 35, 38, 39, 44, 46, 52, 56, 61, 65, 67, 70, 71, 76, 78, 92, 124, 129, 131, 134, 135, 140, 142, 156, 188, 257, 259, 262, 263, 268, 270, 284, 316]
def C : List Nat := [6, 14, 12, 28, 60]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G014


namespace G015
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 60, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 5, 2]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 22, 23, 24, 29, 30, 33, 35, 38, 39, 44, 46, 52, 61, 62, 65, 67, 70, 71, 76, 78, 92, 124, 129, 131, 134, 135, 140, 142, 156, 188, 257, 259, 262, 263, 268, 270, 284, 316]
def C : List Nat := [6, 14, 12, 28, 60]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G015


namespace G016
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 60, 52]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 5, 3]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 22, 23, 24, 29, 30, 33, 35, 38, 39, 44, 46, 56, 61, 62, 65, 67, 70, 71, 76, 78, 92, 124, 129, 131, 134, 135, 140, 142, 156, 188, 257, 259, 262, 263, 268, 270, 284, 316]
def C : List Nat := [6, 14, 12, 28, 60]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G016


namespace G017
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 60, 124]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 5, 6]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 22, 23, 24, 29, 30, 33, 35, 38, 39, 44, 46, 52, 56, 61, 62, 65, 67, 70, 71, 76, 78, 92, 129, 131, 134, 135, 140, 142, 156, 188, 257, 259, 262, 263, 268, 270, 284, 316]
def C : List Nat := [6, 14, 12, 28, 60]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G017


namespace G018
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 27, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 0, 1]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 30, 31, 33, 35, 38, 39, 42, 46, 58, 59, 65, 67, 70, 71, 74, 78, 90, 91, 129, 131, 134, 135, 138, 142, 154, 155, 257, 259, 262, 263, 266, 270, 282, 283]
def C : List Nat := [6, 14, 10, 26, 27]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 12 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    12 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G018


namespace G019
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 27, 31]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 0, 2]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 25, 30, 33, 35, 38, 39, 42, 46, 58, 59, 65, 67, 70, 71, 74, 78, 90, 91, 129, 131, 134, 135, 138, 142, 154, 155, 257, 259, 262, 263, 266, 270, 282, 283]
def C : List Nat := [6, 14, 10, 26, 27]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 11 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    11 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G019


namespace G020
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 27, 59]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 0, 5]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 25, 30, 31, 33, 35, 38, 39, 42, 46, 58, 65, 67, 70, 71, 74, 78, 90, 91, 129, 131, 134, 135, 138, 142, 154, 155, 257, 259, 262, 263, 266, 270, 282, 283]
def C : List Nat := [6, 14, 10, 26, 27]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 17 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    17 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G020


namespace G021
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 24, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 1, 0]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 16, 17, 18, 19, 22, 23, 27, 28, 30, 33, 35, 38, 39, 42, 46, 56, 58, 65, 67, 70, 71, 74, 78, 88, 90, 129, 131, 134, 135, 138, 142, 152, 154, 257, 259, 262, 263, 266, 270, 280, 282]
def C : List Nat := [6, 14, 10, 26, 24]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G021


namespace G022
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 24, 28]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 1, 2]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 16, 17, 18, 19, 22, 23, 25, 27, 30, 33, 35, 38, 39, 42, 46, 56, 58, 65, 67, 70, 71, 74, 78, 88, 90, 129, 131, 134, 135, 138, 142, 152, 154, 257, 259, 262, 263, 266, 270, 280, 282]
def C : List Nat := [6, 14, 10, 26, 24]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 17 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    17 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G022


namespace G023
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 24, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 1, 5]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 16, 17, 18, 19, 22, 23, 25, 27, 28, 30, 33, 35, 38, 39, 42, 46, 58, 65, 67, 70, 71, 74, 78, 88, 90, 129, 131, 134, 135, 138, 142, 152, 154, 257, 259, 262, 263, 266, 270, 280, 282]
def C : List Nat := [6, 14, 10, 26, 24]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 17 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    17 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G023

end Snake9.LocalWindow.ExtendedShare59
