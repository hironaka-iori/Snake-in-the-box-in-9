import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G156
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 54, 118]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 6]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 18, 19, 21, 23, 24, 29, 30, 31, 33, 35, 38, 39, 44, 45, 47, 50, 52, 55, 60, 62, 65, 67, 71, 76, 77, 79, 84, 86, 92, 129, 131, 135, 140, 141, 143, 148, 150, 156, 182, 257, 259, 263, 268, 269, 271, 276, 278, 284, 310]
def C : List Nat := [12, 28, 20, 22, 54]
def mask : Nat := 2085924871461533164452085122440898459077968423282307812480200615455897098778918169861019356020
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 13 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G156


namespace G157
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 60, 62, 63, 59]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 5, 1, 0, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 46, 47, 52, 54, 55, 56, 58, 61, 65, 67, 71, 76, 77, 79, 92, 124, 126, 127, 129, 131, 135, 140, 141, 143, 156, 188, 190, 191, 257, 259, 263, 268, 269, 271, 284, 316, 318, 319]
def C : List Nat := [12, 28, 60, 62, 63]
def mask : Nat := 1735489466716827377329247792665608456496070354722459443042440048041998817122930518840730275433332
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G157


namespace G158
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 60, 62, 63, 55]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 5, 1, 0, 3]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 46, 47, 52, 54, 56, 58, 59, 61, 65, 67, 71, 76, 77, 79, 92, 124, 126, 127, 129, 131, 135, 140, 141, 143, 156, 188, 190, 191, 257, 259, 263, 268, 269, 271, 284, 316, 318, 319]
def C : List Nat := [12, 28, 60, 62, 63]
def mask : Nat := 1735489466716827377329247792665608456496070354722459443042440048041998817122931059272685559892852
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G158


namespace G159
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 60, 62, 63, 127]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 5, 1, 0, 6]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 46, 47, 52, 54, 55, 56, 58, 59, 61, 65, 67, 71, 76, 77, 79, 92, 124, 126, 129, 131, 135, 140, 141, 143, 156, 188, 190, 191, 257, 259, 263, 268, 269, 271, 284, 316, 318, 319]
def C : List Nat := [12, 28, 60, 62, 63]
def mask : Nat := 1735489466716827377329247792665608456496070354722459443042269906858538347891199407997766694751092
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G159


namespace G167
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 22, 18, 50, 48, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 3, 2, 5, 1, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 16, 17, 19, 20, 23, 26, 27, 28, 29, 32, 33, 34, 35, 39, 47, 49, 51, 52, 54, 58, 62, 63, 65, 67, 71, 79, 82, 86, 94, 95, 112, 114, 129, 131, 135, 143, 146, 150, 158, 159, 176, 178, 257, 259, 263, 271, 274, 278, 286, 287, 304, 306]
def C : List Nat := [30, 22, 18, 50, 48]
def mask : Nat := 162963251619017873227359682799026458832919546662271483071817561446376097253699847640286194276
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 13 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G167


namespace G169
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 60, 61, 45, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 37, 39, 44, 46, 47, 52, 53, 54, 56, 57, 58, 63, 65, 67, 71, 79, 94, 95, 109, 124, 125, 126, 129, 131, 135, 143, 158, 159, 173, 188, 189, 190, 257, 259, 263, 271, 286, 287, 301, 316, 317, 318]
def C : List Nat := [30, 62, 60, 61, 45]
def mask : Nat := 934498402660347067581822958083819163034699901410410074798871652422785889495458774629728563915364
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G169


namespace G171
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 60, 61, 45, 109]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 37, 39, 41, 44, 46, 47, 52, 53, 54, 56, 57, 58, 63, 65, 67, 71, 79, 94, 95, 124, 125, 126, 129, 131, 135, 143, 158, 159, 173, 188, 189, 190, 257, 259, 263, 271, 286, 287, 301, 316, 317, 318]
def C : List Nat := [30, 62, 60, 61, 45]
def mask : Nat := 934498402660347067581822958083819163034699901410410074798871651773748782178605321065615546018404
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G171


namespace G174
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 46, 38, 36, 100]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 4, 3, 1, 6]
def D : List Nat := [2, 4, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 32, 33, 34, 35, 37, 39, 42, 44, 47, 52, 54, 58, 60, 63, 65, 67, 71, 79, 94, 95, 102, 110, 126, 129, 131, 135, 143, 158, 159, 164, 166, 174, 190, 257, 259, 263, 271, 286, 287, 292, 294, 302, 318]
def C : List Nat := [30, 62, 46, 38, 36]
def mask : Nat := 534004947282988008887860297498984812047505169955973617452065945048476083658889822233521984006772
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 7 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=7) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G174

end Snake9.LocalWindow.FamilyShare61