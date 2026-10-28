import ExtendedShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G025
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 59]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 0]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 33, 35, 38, 39, 42, 46, 50, 56, 62, 65, 67, 70, 71, 74, 78, 90, 122, 129, 131, 134, 135, 138, 142, 154, 186, 257, 259, 262, 263, 266, 270, 282, 314]
def C : List Nat := [6, 14, 10, 26, 58]
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
end G025


namespace G026
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 1]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 33, 35, 38, 39, 42, 46, 50, 59, 62, 65, 67, 70, 71, 74, 78, 90, 122, 129, 131, 134, 135, 138, 142, 154, 186, 257, 259, 262, 263, 266, 270, 282, 314]
def C : List Nat := [6, 14, 10, 26, 58]
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
end G026


namespace G027
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 62]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 2]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 33, 35, 38, 39, 42, 46, 50, 56, 59, 65, 67, 70, 71, 74, 78, 90, 122, 129, 131, 134, 135, 138, 142, 154, 186, 257, 259, 262, 263, 266, 270, 282, 314]
def C : List Nat := [6, 14, 10, 26, 58]
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
end G027


namespace G028
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 50]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 3]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 33, 35, 38, 39, 42, 46, 56, 59, 62, 65, 67, 70, 71, 74, 78, 90, 122, 129, 131, 134, 135, 138, 142, 154, 186, 257, 259, 262, 263, 266, 270, 282, 314]
def C : List Nat := [6, 14, 10, 26, 58]
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
end G028


namespace G029
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 122]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 6]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 33, 35, 38, 39, 42, 46, 50, 56, 59, 62, 65, 67, 70, 71, 74, 78, 90, 129, 131, 134, 135, 138, 142, 154, 186, 257, 259, 262, 263, 266, 270, 282, 314]
def C : List Nat := [6, 14, 10, 26, 58]
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
end G029


namespace G030
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 29, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 1, 2]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 13, 15, 17, 19, 21, 22, 23, 26, 27, 28, 33, 35, 38, 39, 46, 61, 62, 63, 65, 67, 70, 71, 78, 93, 94, 95, 129, 131, 134, 135, 142, 157, 158, 159, 257, 259, 262, 263, 270, 285, 286, 287]
def C : List Nat := [6, 14, 30, 31, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 18 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    18 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G030


namespace G031
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 29, 21]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 1, 3]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 13, 15, 17, 19, 22, 23, 25, 26, 27, 28, 33, 35, 38, 39, 46, 61, 62, 63, 65, 67, 70, 71, 78, 93, 94, 95, 129, 131, 134, 135, 142, 157, 158, 159, 257, 259, 262, 263, 270, 285, 286, 287]
def C : List Nat := [6, 14, 30, 31, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 23 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    23 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G031


namespace G032
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 29, 13]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 1, 4]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 21, 22, 23, 25, 26, 27, 28, 33, 35, 38, 39, 46, 61, 62, 63, 65, 67, 70, 71, 78, 93, 94, 95, 129, 131, 134, 135, 142, 157, 158, 159, 257, 259, 262, 263, 270, 285, 286, 287]
def C : List Nat := [6, 14, 30, 31, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 18 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    18 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G032


namespace G033
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 29, 61]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 1, 5]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 13, 15, 17, 19, 21, 22, 23, 25, 26, 27, 28, 33, 35, 38, 39, 46, 62, 63, 65, 67, 70, 71, 78, 93, 94, 95, 129, 131, 134, 135, 142, 157, 158, 159, 257, 259, 262, 263, 270, 285, 286, 287]
def C : List Nat := [6, 14, 30, 31, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 27 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    27 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G033


namespace G036
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 63, 61]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 5, 1]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 47, 55, 59, 62, 65, 67, 70, 71, 78, 94, 95, 127, 129, 131, 134, 135, 142, 158, 159, 191, 257, 259, 262, 263, 270, 286, 287, 319]
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
end G036


namespace G037
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 63, 59]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 5, 2]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 47, 55, 61, 62, 65, 67, 70, 71, 78, 94, 95, 127, 129, 131, 134, 135, 142, 158, 159, 191, 257, 259, 262, 263, 270, 286, 287, 319]
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
end G037


namespace G038
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 63, 55]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 5, 3]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 47, 59, 61, 62, 65, 67, 70, 71, 78, 94, 95, 127, 129, 131, 134, 135, 142, 158, 159, 191, 257, 259, 262, 263, 270, 286, 287, 319]
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
end G038

end Snake9.LocalWindow.ExtendedShare59
