import ExtendedShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G080
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 54, 52]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 3, 1]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 50, 55, 58, 60, 63, 65, 67, 70, 71, 78, 94, 118, 126, 129, 131, 134, 135, 142, 158, 182, 190, 257, 259, 262, 263, 270, 286, 310, 318]
def C : List Nat := [6, 14, 30, 62, 54]
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
end G080


namespace G081
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 54, 50]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 3, 2]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 52, 55, 58, 60, 63, 65, 67, 70, 71, 78, 94, 118, 126, 129, 131, 134, 135, 142, 158, 182, 190, 257, 259, 262, 263, 270, 286, 310, 318]
def C : List Nat := [6, 14, 30, 62, 54]
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
end G081


namespace G082
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 54, 118]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 3, 6]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 50, 52, 55, 58, 60, 63, 65, 67, 70, 71, 78, 94, 126, 129, 131, 134, 135, 142, 158, 182, 190, 257, 259, 262, 263, 270, 286, 310, 318]
def C : List Nat := [6, 14, 30, 62, 54]
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
end G082


namespace G089
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 29, 25]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 0, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 21, 23, 24, 30, 31, 33, 35, 39, 44, 46, 47, 60, 61, 65, 67, 71, 76, 78, 79, 92, 93, 129, 131, 135, 140, 142, 143, 156, 157, 257, 259, 263, 268, 270, 271, 284, 285]
def C : List Nat := [15, 14, 12, 28, 29]
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
end G089


namespace G090
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 29, 21]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 0, 3]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 25, 30, 31, 33, 35, 39, 44, 46, 47, 60, 61, 65, 67, 71, 76, 78, 79, 92, 93, 129, 131, 135, 140, 142, 143, 156, 157, 257, 259, 263, 268, 270, 271, 284, 285]
def C : List Nat := [15, 14, 12, 28, 29]
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
end G090


namespace G091
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 29, 61]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 0, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 21, 23, 24, 25, 30, 31, 33, 35, 39, 44, 46, 47, 60, 65, 67, 71, 76, 78, 79, 92, 93, 129, 131, 135, 140, 142, 143, 156, 157, 257, 259, 263, 268, 270, 271, 284, 285]
def C : List Nat := [15, 14, 12, 28, 29]
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
end G091


namespace G092
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 24, 25]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 2, 0]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 16, 17, 19, 20, 23, 26, 29, 30, 31, 33, 35, 39, 44, 46, 47, 56, 60, 65, 67, 71, 76, 78, 79, 88, 92, 129, 131, 135, 140, 142, 143, 152, 156, 257, 259, 263, 268, 270, 271, 280, 284]
def C : List Nat := [15, 14, 12, 28, 24]
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
end G092


namespace G093
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 24, 26]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 2, 1]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 16, 17, 19, 20, 23, 25, 29, 30, 31, 33, 35, 39, 44, 46, 47, 56, 60, 65, 67, 71, 76, 78, 79, 88, 92, 129, 131, 135, 140, 142, 143, 152, 156, 257, 259, 263, 268, 270, 271, 280, 284]
def C : List Nat := [15, 14, 12, 28, 24]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G093


namespace G094
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 2, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 16, 17, 19, 20, 23, 25, 26, 29, 30, 31, 33, 35, 39, 44, 46, 47, 60, 65, 67, 71, 76, 78, 79, 88, 92, 129, 131, 135, 140, 142, 143, 152, 156, 257, 259, 263, 268, 270, 271, 280, 284]
def C : List Nat := [15, 14, 12, 28, 24]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G094


namespace G095
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 20, 21]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 3, 0]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 16, 17, 19, 22, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 60, 65, 67, 71, 76, 78, 79, 84, 92, 129, 131, 135, 140, 142, 143, 148, 156, 257, 259, 263, 268, 270, 271, 276, 284]
def C : List Nat := [15, 14, 12, 28, 20]
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
end G095


namespace G096
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 20, 22]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 3, 1]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 16, 17, 19, 21, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 60, 65, 67, 71, 76, 78, 79, 84, 92, 129, 131, 135, 140, 142, 143, 148, 156, 257, 259, 263, 268, 270, 271, 276, 284]
def C : List Nat := [15, 14, 12, 28, 20]
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
end G096


namespace G097
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 3, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 16, 17, 19, 21, 22, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 60, 65, 67, 71, 76, 78, 79, 84, 92, 129, 131, 135, 140, 142, 143, 148, 156, 257, 259, 263, 268, 270, 271, 276, 284]
def C : List Nat := [15, 14, 12, 28, 20]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 28 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    28 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G097

end Snake9.LocalWindow.ExtendedShare59
