import ExtendedShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G039
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 63, 47]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 5, 4]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 55, 59, 61, 62, 65, 67, 70, 71, 78, 94, 95, 127, 129, 131, 134, 135, 142, 158, 159, 191, 257, 259, 262, 263, 270, 286, 287, 319]
def C : List Nat := [6, 14, 30, 31, 63]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G039


namespace G040
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 63, 127]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 5, 6]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 47, 55, 59, 61, 62, 65, 67, 70, 71, 78, 94, 95, 129, 131, 134, 135, 142, 158, 159, 191, 257, 259, 262, 263, 270, 286, 287, 319]
def C : List Nat := [6, 14, 30, 31, 63]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 10 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G040


namespace G041
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 28, 29, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 1, 0, 2]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 13, 15, 17, 19, 20, 21, 22, 23, 24, 26, 31, 33, 35, 38, 39, 46, 60, 61, 62, 65, 67, 70, 71, 78, 92, 93, 94, 129, 131, 134, 135, 142, 156, 157, 158, 257, 259, 262, 263, 270, 284, 285, 286]
def C : List Nat := [6, 14, 30, 28, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 25 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    25 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G041


namespace G042
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 28, 29, 21]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 1, 0, 3]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 13, 15, 17, 19, 20, 22, 23, 24, 25, 26, 31, 33, 35, 38, 39, 46, 60, 61, 62, 65, 67, 70, 71, 78, 92, 93, 94, 129, 131, 134, 135, 142, 156, 157, 158, 257, 259, 262, 263, 270, 284, 285, 286]
def C : List Nat := [6, 14, 30, 28, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 10 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G042


namespace G043
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 28, 29, 13]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 1, 0, 4]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 20, 21, 22, 23, 24, 25, 26, 31, 33, 35, 38, 39, 46, 60, 61, 62, 65, 67, 70, 71, 78, 92, 93, 94, 129, 131, 134, 135, 142, 156, 157, 158, 257, 259, 262, 263, 270, 284, 285, 286]
def C : List Nat := [6, 14, 30, 28, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 15 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    15 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G043


namespace G044
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 28, 29, 61]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 1, 0, 5]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 13, 15, 17, 19, 20, 21, 22, 23, 24, 25, 26, 31, 33, 35, 38, 39, 46, 60, 62, 65, 67, 70, 71, 78, 92, 93, 94, 129, 131, 134, 135, 142, 156, 157, 158, 257, 259, 262, 263, 270, 284, 285, 286]
def C : List Nat := [6, 14, 30, 28, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 25 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    25 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G044


namespace G045
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 28, 24, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 1, 2, 0]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 12, 15, 16, 17, 19, 20, 22, 23, 26, 29, 31, 33, 35, 38, 39, 46, 56, 60, 62, 65, 67, 70, 71, 78, 88, 92, 94, 129, 131, 134, 135, 142, 152, 156, 158, 257, 259, 262, 263, 270, 280, 284, 286]
def C : List Nat := [6, 14, 30, 28, 24]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 4 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G045


namespace G046
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 28, 24, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 1, 2, 5]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 12, 15, 16, 17, 19, 20, 22, 23, 25, 26, 29, 31, 33, 35, 38, 39, 46, 60, 62, 65, 67, 70, 71, 78, 88, 92, 94, 129, 131, 134, 135, 142, 152, 156, 158, 257, 259, 262, 263, 270, 280, 284, 286]
def C : List Nat := [6, 14, 30, 28, 24]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 4 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G046


namespace G048
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 28, 20, 52]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 1, 3, 5]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 23, 24, 26, 29, 31, 33, 35, 38, 39, 46, 60, 62, 65, 67, 70, 71, 78, 84, 92, 94, 129, 131, 134, 135, 142, 148, 156, 158, 257, 259, 262, 263, 270, 276, 284, 286]
def C : List Nat := [6, 14, 30, 28, 20]
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
end G048


namespace G054
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 1]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 31, 33, 35, 38, 39, 46, 58, 59, 62, 65, 67, 70, 71, 78, 90, 91, 94, 129, 131, 134, 135, 142, 154, 155, 158, 257, 259, 262, 263, 270, 282, 283, 286]
def C : List Nat := [6, 14, 30, 26, 27]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 6 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G054


namespace G055
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 59]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 5]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 25, 28, 31, 33, 35, 38, 39, 46, 58, 62, 65, 67, 70, 71, 78, 90, 91, 94, 129, 131, 134, 135, 142, 154, 155, 158, 257, 259, 262, 263, 270, 282, 283, 286]
def C : List Nat := [6, 14, 30, 26, 27]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 6 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G055


namespace G056
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 24, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 1, 0]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 22, 23, 27, 28, 31, 33, 35, 38, 39, 46, 56, 58, 62, 65, 67, 70, 71, 78, 88, 90, 94, 129, 131, 134, 135, 142, 152, 154, 158, 257, 259, 262, 263, 270, 280, 282, 286]
def C : List Nat := [6, 14, 30, 26, 24]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 22 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    22 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G056

end Snake9.LocalWindow.ExtendedShare59
