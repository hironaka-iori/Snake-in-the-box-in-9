import Port95M60GenericWindow
import Port95M61GeometryBatch03
import Port95M61GeometryBatch04
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G010
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 62, 63, 59]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 2]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G131.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G010
namespace G011
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 62, 63, 55]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 3]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G132.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G011
namespace G012
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 62, 63, 127]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G133.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G012
namespace G013
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 18, 50, 48, 52]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 2, 5, 1, 2]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 16, 17, 19, 20, 23, 26, 28, 31, 32, 33, 34, 35, 39, 46, 47, 49, 51, 54, 56, 58, 62, 65, 67, 71, 78, 79, 82, 86, 94, 112, 114, 129, 131, 135, 142, 143, 146, 150, 158, 176, 178, 257, 259, 263, 270, 271, 274, 278, 286, 304, 306]
def C : List Nat := [30, 22, 18, 50, 48]
def mask : Nat := 162963002959296805924102793653722172440881838385718816347568869729939312266930629540327407204
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
end G013
namespace G014
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 53, 52]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    16≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G136.in_snake p P r hr hP
  exact (by decide : 16≤16).trans h
#print axioms in_snake
end G014
end Snake9.LocalWindow.FamilyCharge67
