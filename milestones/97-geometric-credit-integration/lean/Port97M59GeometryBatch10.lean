import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G170
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 30, 26]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 1, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 22, 23, 24, 29, 31, 33, 35, 39, 44, 45, 47, 60, 62, 65, 67, 71, 76, 77, 79, 92, 94, 129, 131, 135, 140, 141, 143, 156, 158, 257, 259, 263, 268, 269, 271, 284, 286]
def C : List Nat := [15, 13, 12, 28, 30]
def mask : Nat := 155418744485739316941692925412977995173156802448245338446652520933613467231732614450036
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G170


namespace G172
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 30, 62]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 1, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 22, 23, 24, 26, 29, 31, 33, 35, 39, 44, 45, 47, 60, 65, 67, 71, 76, 77, 79, 92, 94, 129, 131, 135, 140, 141, 143, 156, 158, 257, 259, 263, 268, 269, 271, 284, 286]
def C : List Nat := [15, 13, 12, 28, 30]
def mask : Nat := 155418744485739316941692925412977995173156802448245338446652520933608855545714254170996
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G172


namespace G176
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 21]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 0]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 19, 22, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 47, 52, 60, 65, 67, 71, 76, 77, 79, 84, 92, 129, 131, 135, 140, 141, 143, 148, 156, 257, 259, 263, 268, 269, 271, 276, 284]
def C : List Nat := [15, 13, 12, 28, 20]
def mask : Nat := 31209352189056764469779829745449255079342896578939618567014320651425506682545390701428
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 12 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    12 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=12) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G176


namespace G177
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 22]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 1]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 19, 21, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 47, 52, 60, 65, 67, 71, 76, 77, 79, 84, 92, 129, 131, 135, 140, 141, 143, 148, 156, 257, 259, 263, 268, 269, 271, 276, 284]
def C : List Nat := [15, 13, 12, 28, 20]
def mask : Nat := 31209352189056764469779829745449255079342896578939618567014320651425506682545388604276
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 8 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    8 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=8) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G177


namespace G178
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 19, 21, 22, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 47, 60, 65, 67, 71, 76, 77, 79, 84, 92, 129, 131, 135, 140, 141, 143, 148, 156, 257, 259, 263, 268, 269, 271, 276, 284]
def C : List Nat := [15, 13, 12, 28, 20]
def mask : Nat := 31209352189056764469779829745449255079342896578939618567014320651425502178945765428084
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 20 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    20 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=20) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G178


namespace G184
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 30, 26]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 1, 2]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 21, 22, 23, 24, 25, 31, 33, 35, 39, 45, 47, 60, 61, 62, 65, 67, 71, 77, 79, 92, 93, 94, 129, 131, 135, 141, 143, 156, 157, 158, 257, 259, 263, 269, 271, 284, 285, 286]
def C : List Nat := [15, 13, 29, 28, 30]
def mask : Nat := 217583674752565131163979251484576004600225940614926400619581630129860176424756074666596
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=7) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G184


namespace G185
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 30, 22]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 1, 3]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 21, 23, 24, 25, 26, 31, 33, 35, 39, 45, 47, 60, 61, 62, 65, 67, 71, 77, 79, 92, 93, 94, 129, 131, 135, 141, 143, 156, 157, 158, 257, 259, 263, 269, 271, 284, 285, 286]
def C : List Nat := [15, 13, 29, 28, 30]
def mask : Nat := 217583674752565131163979251484576004600225940614926400619581630129860176424756137581156
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 2 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G185


namespace G186
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 30, 62]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 1, 5]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 21, 22, 23, 24, 25, 26, 31, 33, 35, 39, 45, 47, 60, 61, 65, 67, 71, 77, 79, 92, 93, 94, 129, 131, 135, 141, 143, 156, 157, 158, 257, 259, 263, 269, 271, 284, 285, 286]
def C : List Nat := [15, 13, 29, 28, 30]
def mask : Nat := 217583674752565131163979251484576004600225940614926400619581630129855564738737714387556
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=7) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G186


namespace G187
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 24, 26]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 2, 1]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 14, 16, 17, 19, 20, 21, 23, 25, 30, 31, 33, 35, 39, 45, 47, 56, 60, 61, 65, 67, 71, 77, 79, 88, 92, 93, 129, 131, 135, 141, 143, 152, 156, 157, 257, 259, 263, 269, 271, 280, 284, 285]
def C : List Nat := [15, 13, 29, 28, 24]
def mask : Nat := 95195534542344199696053151354694313481394643336079708890671262696384649314706489301860
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 6 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G187


namespace G188
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 2, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 14, 16, 17, 19, 20, 21, 23, 25, 26, 30, 31, 33, 35, 39, 45, 47, 60, 61, 65, 67, 71, 77, 79, 88, 92, 93, 129, 131, 135, 141, 143, 152, 156, 157, 257, 259, 263, 269, 271, 280, 284, 285]
def C : List Nat := [15, 13, 29, 28, 24]
def mask : Nat := 95195534542344199696053151354694313481394643336079708890671262696384577257112518482788
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 6 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G188


namespace G189
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 20, 22]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 3, 1]
def D : List Nat := [2, 4, 5, 6, 9, 11, 12, 14, 16, 17, 19, 21, 23, 24, 25, 30, 31, 33, 35, 39, 45, 47, 52, 60, 61, 65, 67, 71, 77, 79, 84, 92, 93, 129, 131, 135, 141, 143, 148, 156, 157, 257, 259, 263, 269, 271, 276, 284, 285]
def C : List Nat := [15, 13, 29, 28, 20]
def mask : Nat := 93374282455882578692066155817047264506412034745620680739943429847672215875568846723700
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 14 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    14 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=14) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G189


namespace G190
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 3, 5]
def D : List Nat := [2, 4, 5, 6, 9, 11, 12, 14, 16, 17, 19, 21, 22, 23, 24, 25, 30, 31, 33, 35, 39, 45, 47, 60, 61, 65, 67, 71, 77, 79, 84, 92, 93, 129, 131, 135, 141, 143, 148, 156, 157, 257, 259, 263, 269, 271, 276, 284, 285]
def C : List Nat := [15, 13, 29, 28, 20]
def mask : Nat := 93374282455882578692066155817047264506412034745620680739943429847672211371969223547508
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 26 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    26 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=26) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G190

end Snake9.LocalWindow.ExtendedShare59
