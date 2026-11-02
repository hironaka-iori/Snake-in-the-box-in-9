import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G128
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 27, 59]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 0, 5]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 22, 23, 24, 25, 28, 31, 33, 35, 39, 46, 47, 58, 62, 65, 67, 71, 78, 79, 90, 91, 94, 129, 131, 135, 142, 143, 154, 155, 158, 257, 259, 263, 270, 271, 282, 283, 286]
def C : List Nat := [15, 14, 30, 26, 27]
def mask : Nat := 147648543201233916705151532732438515132234907516607250375461352818910860293534175346276
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
end G128


namespace G129
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 24, 25]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 1, 0]
def D : List Nat := [2, 5, 6, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 22, 23, 27, 28, 31, 33, 35, 39, 46, 47, 56, 58, 62, 65, 67, 71, 78, 79, 88, 90, 94, 129, 131, 135, 142, 143, 152, 154, 158, 257, 259, 263, 270, 271, 280, 282, 286]
def C : List Nat := [15, 14, 30, 26, 24]
def mask : Nat := 134049860955653813208715299384673882785698096707846506850026867548525267075392047365988
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 31 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    31 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=31) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G129


namespace G130
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 1, 5]
def D : List Nat := [2, 5, 6, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 22, 23, 25, 27, 28, 31, 33, 35, 39, 46, 47, 58, 62, 65, 67, 71, 78, 79, 88, 90, 94, 129, 131, 135, 142, 143, 152, 154, 158, 257, 259, 263, 270, 271, 280, 282, 286]
def C : List Nat := [15, 14, 30, 26, 24]
def mask : Nat := 134049860955653813208715299384673882785698096707846506850026867548525195017798042992484
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 42 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    42 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=42) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G130


namespace G131
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 18, 50]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 3, 5]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 16, 17, 19, 22, 23, 24, 27, 28, 31, 33, 35, 39, 46, 47, 58, 62, 65, 67, 71, 78, 79, 82, 90, 94, 129, 131, 135, 142, 143, 146, 154, 158, 257, 259, 263, 270, 271, 274, 282, 286]
def C : List Nat := [15, 14, 30, 26, 18]
def mask : Nat := 132137546264869111154528954070144481361966357687864527291762643057377210838397615816292
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
end G131


namespace G132
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 58, 59]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 5, 0]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 39, 42, 46, 47, 50, 56, 62, 65, 67, 71, 78, 79, 90, 94, 122, 129, 131, 135, 142, 143, 154, 158, 186, 257, 259, 263, 270, 271, 282, 286, 314]
def C : List Nat := [15, 14, 30, 26, 58]
def mask : Nat := 33374797568371412100850298296695089268615701755488097295386319733193455176464179490664055979620
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
end G132


namespace G133
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 58, 56]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 5, 1]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 39, 42, 46, 47, 50, 59, 62, 65, 67, 71, 78, 79, 90, 94, 122, 129, 131, 135, 142, 143, 154, 158, 186, 257, 259, 263, 270, 271, 282, 286, 314]
def C : List Nat := [15, 14, 30, 26, 58]
def mask : Nat := 33374797568371412100850298296695089268615701755488097295386319733193455176464683893822321475172
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
end G133


namespace G134
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 58, 50]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 5, 3]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 39, 42, 46, 47, 56, 59, 62, 65, 67, 71, 78, 79, 90, 94, 122, 129, 131, 135, 142, 143, 154, 158, 186, 257, 259, 263, 270, 271, 282, 286, 314]
def C : List Nat := [15, 14, 30, 26, 58]
def mask : Nat := 33374797568371412100850298296695089268615701755488097295386319733193455176464754825516452560484
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
end G134


namespace G135
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 58, 42]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 5, 4]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 39, 46, 47, 50, 56, 59, 62, 65, 67, 71, 78, 79, 90, 94, 122, 129, 131, 135, 142, 143, 154, 158, 186, 257, 259, 263, 270, 271, 282, 286, 314]
def C : List Nat := [15, 14, 30, 26, 58]
def mask : Nat := 33374797568371412100850298296695089268615701755488097295386319733193455176464755947018312892004
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
end G135


namespace G136
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 58, 122]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 5, 6]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 39, 42, 46, 47, 50, 56, 59, 62, 65, 67, 71, 78, 79, 90, 94, 129, 131, 135, 142, 143, 154, 158, 186, 257, 259, 263, 270, 271, 282, 286, 314]
def C : List Nat := [15, 14, 30, 26, 58]
def mask : Nat := 33374797568371412100850298296695089268615701755488097295381002821210315512973140723175238024804
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
end G136


namespace G137
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 20, 21]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 1, 0]
def D : List Nat := [2, 4, 5, 6, 9, 10, 11, 12, 13, 16, 17, 18, 19, 23, 26, 28, 31, 33, 35, 39, 46, 47, 52, 54, 62, 65, 67, 71, 78, 79, 84, 86, 94, 129, 131, 135, 142, 143, 148, 150, 158, 257, 259, 263, 270, 271, 276, 278, 286]
def C : List Nat := [15, 14, 30, 22, 20]
def mask : Nat := 124943600523345708188780321696438637910785053755551366096387703304963099879703684529780
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
end G137


namespace G138
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 1, 5]
def D : List Nat := [2, 4, 5, 6, 9, 10, 11, 12, 13, 16, 17, 18, 19, 21, 23, 26, 28, 31, 33, 35, 39, 46, 47, 54, 62, 65, 67, 71, 78, 79, 84, 86, 94, 129, 131, 135, 142, 143, 148, 150, 158, 257, 259, 263, 270, 271, 276, 278, 286]
def C : List Nat := [15, 14, 30, 22, 20]
def mask : Nat := 124943600523345708188780321696438637910785053755551366096387703304963095376104059256436
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 18 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    18 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=18) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G138


namespace G140
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 54, 55]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 5, 0]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 20, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 50, 52, 62, 65, 67, 71, 78, 79, 86, 94, 118, 129, 131, 135, 142, 143, 150, 158, 182, 257, 259, 263, 270, 271, 278, 286, 310]
def C : List Nat := [15, 14, 30, 22, 54]
def mask : Nat := 2085924964588697469920488506779058564185001596396928792272604401585615031709282961189347671652
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
end G140

end Snake9.LocalWindow.ExtendedShare59
