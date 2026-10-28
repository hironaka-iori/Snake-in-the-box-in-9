import GenericWindow
namespace Snake9.LocalWindow.CriticalExtension60
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace T00
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 60, 62, 63]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 5, 1, 0]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 46, 47, 52, 54, 56, 58, 61, 65, 67, 71, 76, 77, 79, 92, 124, 126, 129, 131, 135, 140, 141, 143, 156, 188, 190, 257, 259, 263, 268, 269, 271, 284, 316, 318]
def C : List Nat := [13, 12, 28, 60, 62]
def mask : Nat := 667495948756372336131736939580832399191579542676439717686831208235824651792827342774504311638900
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T00


namespace T01
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 51]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 2]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 53, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 119, 126, 127, 129, 131, 134, 135, 142, 158, 183, 190, 191, 257, 259, 262, 263, 270, 286, 311, 318, 319]
def C : List Nat := [14, 30, 62, 63, 55]
def mask : Nat := 1606162126744548318930982807062289349815644449426703425674142263894521352053554578545599075491380
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T01


namespace T02
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 49, 53]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 1, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 48, 50, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 113, 115, 123, 127, 129, 131, 135, 143, 159, 177, 179, 187, 191, 257, 259, 263, 271, 287, 305, 307, 315, 319]
def C : List Nat := [31, 63, 59, 51, 49]
def mask : Nat := 1135069038837862427505539996917137793492033796486850206287758984303992112630987933854150695742052
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T02


namespace T03
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 24, 26, 10]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 0, 1, 4]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 18, 19, 21, 23, 27, 28, 30, 33, 35, 39, 47, 56, 57, 58, 61, 63, 65, 67, 71, 79, 88, 89, 90, 93, 95, 129, 131, 135, 143, 152, 153, 154, 157, 159, 257, 259, 263, 271, 280, 281, 282, 285, 287]
def C : List Nat := [31, 29, 25, 24, 26]
def mask : Nat := 324429515256185197970276746466360353294531174479881854718452653174714233795081751456612
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 10 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T03


namespace T04
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 29, 21, 53]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 0, 3, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 25, 30, 31, 33, 35, 39, 44, 46, 47, 60, 61, 65, 67, 71, 76, 78, 79, 85, 92, 93, 129, 131, 135, 140, 142, 143, 149, 156, 157, 257, 259, 263, 268, 270, 271, 277, 284, 285]
def C : List Nat := [14, 12, 28, 29, 21]
def mask : Nat := 93497122114839234900407987026487521195089247147945912065734708156999425686269761040244
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 9 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    9 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T04


namespace T05
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 18, 50, 34]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 2, 5, 4]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 16, 17, 19, 20, 23, 26, 28, 31, 33, 35, 39, 46, 47, 48, 51, 54, 58, 62, 65, 67, 71, 78, 79, 82, 86, 94, 114, 129, 131, 135, 142, 143, 146, 150, 158, 178, 257, 259, 263, 270, 271, 274, 278, 286, 306]
def C : List Nat := [14, 30, 22, 18, 50]
def mask : Nat := 130370427337945028543807662639172121863962563115759718283738033554213782319040201459437878884
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T05


namespace T06
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 41, 45]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 4, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 40, 43, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 91, 95, 105, 121, 129, 131, 135, 143, 153, 155, 159, 169, 185, 257, 259, 263, 271, 281, 283, 287, 297, 313]
def C : List Nat := [31, 27, 25, 57, 41]
def mask : Nat := 16687653615721269211110945548773028236131106121792920179150929056317451243530772661256202119780
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 8 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    8 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=8) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T06


namespace T07
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 54]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 1, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 18, 19, 21, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 47, 52, 60, 65, 67, 71, 76, 77, 79, 84, 86, 92, 129, 131, 135, 140, 141, 143, 148, 150, 156, 257, 259, 263, 268, 269, 271, 276, 278, 284]
def C : List Nat := [13, 12, 28, 20, 22]
def mask : Nat := 31695019412113196737509695222155134806004925536395359407208409411082137585250254932852
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 14 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    14 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=14) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T07


namespace T08
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 59, 57]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 5, 1]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 25, 28, 31, 33, 35, 38, 39, 43, 46, 51, 58, 62, 63, 65, 67, 70, 71, 78, 90, 91, 94, 123, 129, 131, 134, 135, 142, 154, 155, 158, 187, 257, 259, 262, 263, 270, 282, 283, 286, 315]
def C : List Nat := [14, 30, 26, 27, 59]
def mask : Nat := 66749595020173196411591927834094903848475466755772695881159769971969382021738657611907127483956
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T08


namespace T09
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 56, 60]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 0, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 40, 41, 47, 48, 49, 58, 59, 61, 63, 65, 67, 71, 79, 89, 93, 95, 120, 121, 129, 131, 135, 143, 153, 157, 159, 184, 185, 257, 259, 263, 271, 281, 285, 287, 312, 313]
def C : List Nat := [31, 29, 25, 57, 56]
def mask : Nat := 25031098391914335823123213234853875775316762168619182643789120097528084981506269221305342126692
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T09

end Snake9.LocalWindow.CriticalExtension60