import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G443
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 43, 107]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 41, 42, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 123, 127, 129, 131, 135, 143, 159, 171, 187, 191, 257, 259, 263, 271, 287, 299, 315, 319]
def C : List Nat := [15, 31, 63, 59, 43]
def mask : Nat := 1134744131599637076974780179829836497675345132461502801528935170493606071925107259730175541799524
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 11 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    11 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=11) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G443


namespace G444
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 123, 122]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 6, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 91, 95, 107, 115, 121, 127, 129, 131, 135, 143, 159, 187, 191, 251, 257, 259, 263, 271, 287, 315, 319, 379]
def C : List Nat := [15, 31, 63, 59, 123]
def mask : Nat := 1231312693637327476518463116211136841144097400597703632466635365898350917786815260902393856915571956637862795569764
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G444


namespace G445
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 123, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 6, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 91, 95, 107, 115, 122, 127, 129, 131, 135, 143, 159, 187, 191, 251, 257, 259, 263, 271, 287, 315, 319, 379]
def C : List Nat := [15, 31, 63, 59, 123]
def mask : Nat := 1231312693637327476518463116211136841144097400597703632466635365898350917786817919358385426747317764251983356258916
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G445


namespace G446
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 123, 115]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 6, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 91, 95, 107, 121, 122, 127, 129, 131, 135, 143, 159, 187, 191, 251, 257, 259, 263, 271, 287, 315, 319, 379]
def C : List Nat := [15, 31, 63, 59, 123]
def mask : Nat := 1231312693637327476518463116211136841144097400597703632466635365898350917786820536276002128300442543622133283187300
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G446


namespace G447
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 123, 107]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 6, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 91, 95, 115, 121, 122, 127, 129, 131, 135, 143, 159, 187, 191, 251, 257, 259, 263, 271, 287, 315, 319, 379]
def C : List Nat := [15, 31, 63, 59, 123]
def mask : Nat := 1231312693637327476518463116211136841144097400597703632466635365898350917786820577652117719749850208474525906659940
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G447


namespace G448
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 123, 91]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 6, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 107, 115, 121, 122, 127, 129, 131, 135, 143, 159, 187, 191, 251, 257, 259, 263, 271, 287, 315, 319, 379]
def C : List Nat := [15, 31, 63, 59, 123]
def mask : Nat := 1231312693637327476518463116211136841144097400597703632466635365898350917786820577814374520698985001105554118699620
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G448


namespace G449
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 123, 251]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 6, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 91, 95, 107, 115, 121, 122, 127, 129, 131, 135, 143, 159, 187, 191, 257, 259, 263, 271, 287, 315, 319, 379]
def C : List Nat := [15, 31, 63, 59, 123]
def mask : Nat := 1231312693637327476518463116211136841140478897809037501359648772616829420666405890793575728952830522365856631646820
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G449


namespace G450
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 54, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 0, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 27, 29, 30, 33, 35, 38, 39, 47, 50, 51, 53, 59, 61, 62, 65, 67, 71, 79, 95, 118, 119, 127, 129, 131, 135, 143, 159, 182, 183, 191, 257, 259, 263, 271, 287, 310, 311, 319]
def C : List Nat := [15, 31, 63, 55, 54]
def mask : Nat := 1074251292728420010913909282443987399115502428833106529300650644000088273748359498853458134067812
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 10 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G450


namespace G451
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 54, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 0, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 27, 29, 30, 33, 35, 38, 39, 47, 51, 52, 53, 59, 61, 62, 65, 67, 71, 79, 95, 118, 119, 127, 129, 131, 135, 143, 159, 182, 183, 191, 257, 259, 263, 271, 287, 310, 311, 319]
def C : List Nat := [15, 31, 63, 55, 54]
def mask : Nat := 1074251292728420010913909282443987399115502428833106529300650644000088273748359502231157854595684
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 10 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G451


namespace G452
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 54, 38]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 0, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 27, 29, 30, 33, 35, 39, 47, 50, 51, 52, 53, 59, 61, 62, 65, 67, 71, 79, 95, 118, 119, 127, 129, 131, 135, 143, 159, 182, 183, 191, 257, 259, 263, 271, 287, 310, 311, 319]
def C : List Nat := [15, 31, 63, 55, 54]
def mask : Nat := 1074251292728420010913909282443987399115502428833106529300650644000088273748359503356782883531364
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 10 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G452


namespace G453
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 54, 22]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 0, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 38, 39, 47, 50, 51, 52, 53, 59, 61, 62, 65, 67, 71, 79, 95, 118, 119, 127, 129, 131, 135, 143, 159, 182, 183, 191, 257, 259, 263, 271, 287, 310, 311, 319]
def C : List Nat := [15, 31, 63, 55, 54]
def mask : Nat := 1074251292728420010913909282443987399115502428833106529300650644000088273748359503357057757244004
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
end G453


namespace G454
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 54, 118]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 0, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 27, 29, 30, 33, 35, 38, 39, 47, 50, 51, 52, 53, 59, 61, 62, 65, 67, 71, 79, 95, 119, 127, 129, 131, 135, 143, 159, 182, 183, 191, 257, 259, 263, 271, 287, 310, 311, 319]
def C : List Nat := [15, 31, 63, 55, 54]
def mask : Nat := 1074251292728420010913909282443987399115502428833106529300650311693089327519391277405292691352164
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 10 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G454

end Snake9.LocalWindow.ExtendedShare59
