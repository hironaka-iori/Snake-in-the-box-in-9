import GenericWindow
import GeometryBatch10
import GeometryBatch11
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G055
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 99, 98]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 4, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G281.in_snake p P r hr hP
  exact (by decide : 5≤5).trans h
#print axioms in_snake
end G055
namespace G056
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 99, 227]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 4, 7]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G282.in_snake p P r hr hP
  exact (by decide : 5≤5).trans h
#print axioms in_snake
end G056
namespace G057
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 83, 91]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 5, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 81, 82, 87, 95, 99, 113, 114, 119, 123, 127, 129, 131, 135, 143, 159, 179, 183, 191, 211, 243, 257, 259, 263, 271, 287, 307, 311, 319, 339, 371]
def C : List Nat := [63, 55, 51, 115, 83]
def mask : Nat := 4809815210640683894232666861127594752976509882919176210772114887227031729495089214242900069562303711599089314404
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 13≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    13≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G057
namespace G058
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 125, 93, 77, 76]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G301.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G058
namespace G059
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 125, 93, 77, 73]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 2]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G299.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G059
end Snake9.LocalWindow.FamilyCharge67
