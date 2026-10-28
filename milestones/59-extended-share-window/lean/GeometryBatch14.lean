import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G228
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 53, 49]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 3, 2]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 37, 39, 45, 47, 52, 55, 57, 60, 63, 65, 67, 71, 77, 79, 93, 117, 125, 129, 131, 135, 141, 143, 157, 181, 189, 257, 259, 263, 269, 271, 285, 309, 317]
def C : List Nat := [15, 13, 29, 61, 53]
def mask : Nat := 268041341972167180550053962954081914883278611888520296706034128466639985330596741906980592573028
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 24 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    24 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=24) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G228


namespace G229
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 53, 37]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 3, 4]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 49, 52, 55, 57, 60, 63, 65, 67, 71, 77, 79, 93, 117, 125, 129, 131, 135, 141, 143, 157, 181, 189, 257, 259, 263, 269, 271, 285, 309, 317]
def C : List Nat := [15, 13, 29, 61, 53]
def mask : Nat := 268041341972167180550053962954081914883278611888520296706034128466639985330596742469793107040868
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 21 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    21 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=21) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G229


namespace G230
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 53, 117]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 3, 6]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 37, 39, 45, 47, 49, 52, 55, 57, 60, 63, 65, 67, 71, 77, 79, 93, 125, 129, 131, 135, 141, 143, 157, 181, 189, 257, 259, 263, 269, 271, 285, 309, 317]
def C : List Nat := [15, 13, 29, 61, 53]
def mask : Nat := 268041341972167180550053962954081914883278611888520296706033962313140512216112629494048010951268
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 29 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    29 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=29) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G230


namespace G231
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 125, 124]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 6, 0]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 77, 79, 93, 109, 117, 121, 127, 129, 131, 135, 141, 143, 157, 189, 253, 257, 259, 263, 269, 271, 285, 317, 381]
def C : List Nat := [15, 13, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392070235649323325938724461671186300243736682815486932047365128622924695324269872650279524
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
end G231


namespace G232
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 125, 127]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 6, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 77, 79, 93, 109, 117, 121, 124, 129, 131, 135, 141, 143, 157, 189, 253, 257, 259, 263, 269, 271, 285, 317, 381]
def C : List Nat := [15, 13, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392070235649323325938724461671186300243736682815486783173829600712346930097879121251687012
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
end G232


namespace G233
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 125, 121]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 6, 2]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 77, 79, 93, 109, 117, 124, 127, 129, 131, 135, 141, 143, 157, 189, 253, 257, 259, 263, 269, 271, 285, 317, 381]
def C : List Nat := [15, 13, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392070235649323325938724461671186300243736682815486950656557069611746915977568716575103588
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
end G233


namespace G234
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 125, 117]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 6, 3]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 77, 79, 93, 109, 121, 124, 127, 129, 131, 135, 141, 143, 157, 189, 253, 257, 259, 263, 269, 271, 285, 317, 381]
def C : List Nat := [15, 13, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392070235649323325938724461671186300243736682815486953148859561708464177672206954600749668
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
end G234


namespace G235
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 125, 109]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 6, 4]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 77, 79, 93, 117, 121, 124, 127, 129, 131, 135, 141, 143, 157, 189, 253, 257, 259, 263, 269, 271, 285, 317, 381]
def C : List Nat := [15, 13, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392070235649323325938724461671186300243736682815486953314364024074261808331616525094640228
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
end G235


namespace G236
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 125, 253]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 6, 7]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 77, 79, 93, 109, 117, 121, 124, 127, 129, 131, 135, 141, 143, 157, 189, 257, 259, 263, 269, 271, 285, 317, 381]
def C : List Nat := [15, 13, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392070235649308851927569797146758353870610596827005294566929856111073729587181847994587748
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
end G236


namespace G237
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 28, 24, 25]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 1, 2, 0]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 14, 16, 17, 19, 20, 22, 23, 26, 27, 29, 33, 35, 39, 47, 56, 60, 62, 63, 65, 67, 71, 79, 88, 92, 94, 95, 129, 131, 135, 143, 152, 156, 158, 159, 257, 259, 263, 271, 280, 284, 286, 287]
def C : List Nat := [15, 31, 30, 28, 24]
def mask : Nat := 406021608729665818948894146552948147373752039332446315871059564797031251868448108280676
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
end G237


namespace G238
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 28, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 1, 2, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 14, 16, 17, 19, 20, 22, 23, 25, 26, 27, 29, 33, 35, 39, 47, 60, 62, 63, 65, 67, 71, 79, 88, 92, 94, 95, 129, 131, 135, 143, 152, 156, 158, 159, 257, 259, 263, 271, 280, 284, 286, 287]
def C : List Nat := [15, 31, 30, 28, 24]
def mask : Nat := 406021608729665818948894146552948147373752039332446315871059564797031179810854103907172
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 21 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    21 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=21) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G238


namespace G239
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 28, 20, 21]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 1, 3, 0]
def D : List Nat := [2, 4, 5, 6, 9, 11, 12, 13, 14, 16, 17, 19, 22, 23, 24, 26, 27, 29, 33, 35, 39, 47, 52, 60, 62, 63, 65, 67, 71, 79, 84, 92, 94, 95, 129, 131, 135, 143, 148, 156, 158, 159, 257, 259, 263, 271, 276, 284, 286, 287]
def C : List Nat := [15, 31, 30, 28, 20]
def mask : Nat := 404200356643204197944907151015301098398769430741987287720331731948318818429310465702516
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
end G239

end Snake9.LocalWindow.ExtendedShare59
