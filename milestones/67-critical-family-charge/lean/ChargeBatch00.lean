import GenericWindow
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G000
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 56, 40, 44]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 1, 4, 2]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 32, 33, 35, 38, 39, 41, 42, 46, 48, 50, 57, 59, 60, 62, 65, 67, 70, 71, 74, 78, 90, 104, 120, 122, 129, 131, 134, 135, 138, 142, 154, 168, 184, 186, 257, 259, 262, 263, 266, 270, 282, 296, 312, 314]
def C : List Nat := [10, 26, 58, 56, 40]
def mask : Nat := 41718624117851510619752544898358847036931817057116434195524578995296986678499473045753638591284
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G000
namespace G001
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 62, 54, 55]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 0]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 33, 35, 38, 39, 42, 46, 50, 52, 56, 59, 60, 63, 65, 67, 70, 71, 74, 78, 90, 118, 122, 126, 129, 131, 134, 135, 138, 142, 154, 182, 186, 190, 257, 259, 262, 263, 266, 270, 282, 310, 314, 318]
def C : List Nat := [10, 26, 58, 62, 54]
def mask : Nat := 569457481264030969056110914508097740392273656137375126767346666513440956165723155162246903929652
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 4≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=4) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G001
namespace G002
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 62, 54, 52]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 1]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 33, 35, 38, 39, 42, 46, 50, 55, 56, 59, 60, 63, 65, 67, 70, 71, 74, 78, 90, 118, 122, 126, 129, 131, 134, 135, 138, 142, 154, 182, 186, 190, 257, 259, 262, 263, 266, 270, 282, 310, 314, 318]
def C : List Nat := [10, 26, 58, 62, 54]
def mask : Nat := 569457481264030969056110914508097740392273656137375126767346666513440956165723186687444295523124
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 4≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=4) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G002
namespace G003
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 62, 54, 118]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 6]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 33, 35, 38, 39, 42, 46, 50, 52, 55, 56, 59, 60, 63, 65, 67, 70, 71, 74, 78, 90, 122, 126, 129, 131, 134, 135, 138, 142, 154, 182, 186, 190, 257, 259, 262, 263, 266, 270, 282, 310, 314, 318]
def C : List Nat := [10, 26, 58, 62, 54]
def mask : Nat := 569457481264030969056110914508097740392273656137375126767346334206442009936754965239278852807476
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 4≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=4) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G003
namespace G004
def W : List Nat := [0, 1, 3, 7, 6, 14, 10, 26, 58, 122, 106, 110]
def ds : List Nat := [0, 1, 2, 0, 3, 2, 4, 5, 6, 4, 2]
def D : List Nat := [2, 4, 5, 8, 9, 11, 12, 15, 17, 18, 19, 22, 23, 24, 27, 30, 33, 35, 38, 39, 42, 46, 50, 56, 59, 62, 65, 67, 70, 71, 74, 78, 90, 98, 104, 107, 114, 120, 123, 126, 129, 131, 134, 135, 138, 142, 154, 186, 234, 250, 257, 259, 262, 263, 266, 270, 282, 314, 362, 378]
def C : List Nat := [10, 26, 58, 122, 106]
def mask : Nat := 615665740988994833058146356931168057759306307413315198685028776482097610997602338330820919524701517674704492469044
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G004
end Snake9.LocalWindow.FamilyCharge67
