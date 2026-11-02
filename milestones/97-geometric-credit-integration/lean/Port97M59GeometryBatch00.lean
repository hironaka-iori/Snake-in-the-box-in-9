import Port95M59ExtendedShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G000
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 13, 29, 31]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 0, 4, 1]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 15, 17, 19, 21, 22, 23, 25, 28, 30, 33, 35, 38, 39, 44, 45, 46, 61, 65, 67, 70, 71, 76, 77, 78, 93, 129, 131, 134, 135, 140, 141, 142, 157, 257, 259, 262, 263, 268, 269, 270, 285]
def C : List Nat := [6, 14, 12, 13, 29]
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
end G000


namespace G001
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 13, 29, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 0, 4, 2]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 15, 17, 19, 21, 22, 23, 28, 30, 31, 33, 35, 38, 39, 44, 45, 46, 61, 65, 67, 70, 71, 76, 77, 78, 93, 129, 131, 134, 135, 140, 141, 142, 157, 257, 259, 262, 263, 268, 269, 270, 285]
def C : List Nat := [6, 14, 12, 13, 29]
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
end G001


namespace G002
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 13, 29, 21]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 0, 4, 3]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 15, 17, 19, 22, 23, 25, 28, 30, 31, 33, 35, 38, 39, 44, 45, 46, 61, 65, 67, 70, 71, 76, 77, 78, 93, 129, 131, 134, 135, 140, 141, 142, 157, 257, 259, 262, 263, 268, 269, 270, 285]
def C : List Nat := [6, 14, 12, 13, 29]
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
end G002


namespace G003
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 13, 29, 61]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 0, 4, 5]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 15, 17, 19, 21, 22, 23, 25, 28, 30, 31, 33, 35, 38, 39, 44, 45, 46, 65, 67, 70, 71, 76, 77, 78, 93, 129, 131, 134, 135, 140, 141, 142, 157, 257, 259, 262, 263, 268, 269, 270, 285]
def C : List Nat := [6, 14, 12, 13, 29]
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
end G003


namespace G004
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 29, 31]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 0, 1]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 21, 22, 23, 24, 25, 30, 33, 35, 38, 39, 44, 46, 60, 61, 65, 67, 70, 71, 76, 78, 92, 93, 129, 131, 134, 135, 140, 142, 156, 157, 257, 259, 262, 263, 268, 270, 284, 285]
def C : List Nat := [6, 14, 12, 28, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 29 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    29 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G004


namespace G005
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 29, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 0, 2]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 21, 22, 23, 24, 30, 31, 33, 35, 38, 39, 44, 46, 60, 61, 65, 67, 70, 71, 76, 78, 92, 93, 129, 131, 134, 135, 140, 142, 156, 157, 257, 259, 262, 263, 268, 270, 284, 285]
def C : List Nat := [6, 14, 12, 28, 29]
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
end G005


namespace G006
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 29, 21]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 0, 3]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 22, 23, 24, 25, 30, 31, 33, 35, 38, 39, 44, 46, 60, 61, 65, 67, 70, 71, 76, 78, 92, 93, 129, 131, 134, 135, 140, 142, 156, 157, 257, 259, 262, 263, 268, 270, 284, 285]
def C : List Nat := [6, 14, 12, 28, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 21 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    21 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G006


namespace G007
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 29, 61]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 0, 5]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 17, 19, 20, 21, 22, 23, 24, 25, 30, 31, 33, 35, 38, 39, 44, 46, 60, 65, 67, 70, 71, 76, 78, 92, 93, 129, 131, 134, 135, 140, 142, 156, 157, 257, 259, 262, 263, 268, 270, 284, 285]
def C : List Nat := [6, 14, 12, 28, 29]
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 36 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    36 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end G007


namespace G008
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 24, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 2, 0]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 16, 17, 19, 20, 22, 23, 26, 29, 30, 33, 35, 38, 39, 44, 46, 56, 60, 65, 67, 70, 71, 76, 78, 88, 92, 129, 131, 134, 135, 140, 142, 152, 156, 257, 259, 262, 263, 268, 270, 280, 284]
def C : List Nat := [6, 14, 12, 28, 24]
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
end G008


namespace G009
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 24, 26]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 2, 1]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 16, 17, 19, 20, 22, 23, 25, 29, 30, 33, 35, 38, 39, 44, 46, 56, 60, 65, 67, 70, 71, 76, 78, 88, 92, 129, 131, 134, 135, 140, 142, 152, 156, 257, 259, 262, 263, 268, 270, 280, 284]
def C : List Nat := [6, 14, 12, 28, 24]
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
end G009


namespace G010
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 24, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 2, 5]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 16, 17, 19, 20, 22, 23, 25, 26, 29, 30, 33, 35, 38, 39, 44, 46, 60, 65, 67, 70, 71, 76, 78, 88, 92, 129, 131, 134, 135, 140, 142, 152, 156, 257, 259, 262, 263, 268, 270, 280, 284]
def C : List Nat := [6, 14, 12, 28, 24]
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
end G010


namespace G011
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 28, 20, 21]
def ds : List Nat := [0, 1, 2, 0, 3, 1, 4, 3, 0]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 13, 15, 16, 17, 19, 22, 23, 24, 29, 30, 33, 35, 38, 39, 44, 46, 52, 60, 65, 67, 70, 71, 76, 78, 84, 92, 129, 131, 134, 135, 140, 142, 148, 156, 257, 259, 262, 263, 268, 270, 276, 284]
def C : List Nat := [6, 14, 12, 28, 20]
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
end G011

end Snake9.LocalWindow.ExtendedShare59
