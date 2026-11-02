import Port95M59ExtendedShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G057
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 24, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 1, 5]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 22, 23, 25, 27, 28, 31, 33, 35, 38, 39, 46, 58, 62, 65, 67, 70, 71, 78, 88, 90, 94, 129, 131, 134, 135, 142, 152, 154, 158, 257, 259, 262, 263, 270, 280, 282, 286]
def C : List Nat := [6, 14, 30, 26, 24]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 31 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    31 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G057


namespace G058
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 18, 50]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 3, 5]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 16, 17, 19, 22, 23, 24, 27, 28, 31, 33, 35, 38, 39, 46, 58, 62, 65, 67, 70, 71, 78, 82, 90, 94, 129, 131, 134, 135, 142, 146, 154, 158, 257, 259, 262, 263, 270, 274, 282, 286]
def C : List Nat := [6, 14, 30, 26, 18]
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
end G058


namespace G059
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 58, 59]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 5, 0]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 38, 39, 42, 46, 50, 56, 62, 65, 67, 70, 71, 78, 90, 94, 122, 129, 131, 134, 135, 142, 154, 158, 186, 257, 259, 262, 263, 270, 282, 286, 314]
def C : List Nat := [6, 14, 30, 26, 58]
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
end G059


namespace G060
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 58, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 5, 1]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 38, 39, 42, 46, 50, 59, 62, 65, 67, 70, 71, 78, 90, 94, 122, 129, 131, 134, 135, 142, 154, 158, 186, 257, 259, 262, 263, 270, 282, 286, 314]
def C : List Nat := [6, 14, 30, 26, 58]
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
end G060


namespace G061
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 58, 50]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 5, 3]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 38, 39, 42, 46, 56, 59, 62, 65, 67, 70, 71, 78, 90, 94, 122, 129, 131, 134, 135, 142, 154, 158, 186, 257, 259, 262, 263, 270, 282, 286, 314]
def C : List Nat := [6, 14, 30, 26, 58]
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
end G061


namespace G062
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 58, 42]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 5, 4]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 38, 39, 46, 50, 56, 59, 62, 65, 67, 70, 71, 78, 90, 94, 122, 129, 131, 134, 135, 142, 154, 158, 186, 257, 259, 262, 263, 270, 282, 286, 314]
def C : List Nat := [6, 14, 30, 26, 58]
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
end G062


namespace G063
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 58, 122]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 5, 6]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 38, 39, 42, 46, 50, 56, 59, 62, 65, 67, 70, 71, 78, 90, 94, 129, 131, 134, 135, 142, 154, 158, 186, 257, 259, 262, 263, 270, 282, 286, 314]
def C : List Nat := [6, 14, 30, 26, 58]
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
end G063


namespace G064
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 61]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 1]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 54, 55, 58, 59, 60, 65, 67, 70, 71, 78, 94, 126, 127, 129, 131, 134, 135, 142, 158, 190, 191, 257, 259, 262, 263, 270, 286, 318, 319]
def C : List Nat := [6, 14, 30, 62, 63]
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
end G064


namespace G065
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 59]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 2]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 54, 55, 58, 60, 61, 65, 67, 70, 71, 78, 94, 126, 127, 129, 131, 134, 135, 142, 158, 190, 191, 257, 259, 262, 263, 270, 286, 318, 319]
def C : List Nat := [6, 14, 30, 62, 63]
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
end G065


namespace G066
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 126, 127, 129, 131, 134, 135, 142, 158, 190, 191, 257, 259, 262, 263, 270, 286, 318, 319]
def C : List Nat := [6, 14, 30, 62, 63]
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
end G066


namespace G067
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 47]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 4]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 54, 55, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 126, 127, 129, 131, 134, 135, 142, 158, 190, 191, 257, 259, 262, 263, 270, 286, 318, 319]
def C : List Nat := [6, 14, 30, 62, 63]
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
end G067


namespace G068
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 127]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 6]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 54, 55, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 126, 129, 131, 134, 135, 142, 158, 190, 191, 257, 259, 262, 263, 270, 286, 318, 319]
def C : List Nat := [6, 14, 30, 62, 63]
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
end G068

end Snake9.LocalWindow.ExtendedShare59
