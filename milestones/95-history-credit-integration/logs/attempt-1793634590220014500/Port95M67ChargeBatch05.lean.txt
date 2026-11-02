import Port95M60GenericWindow
import Port95M61GeometryBatch05
import Port95M61GeometryBatch06
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G025
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 125, 109, 111, 239]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 6, 4, 1, 7]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 77, 79, 93, 101, 103, 105, 107, 108, 110, 117, 121, 124, 127, 129, 131, 135, 141, 143, 157, 189, 237, 253, 257, 259, 263, 269, 271, 285, 317, 365, 367, 381]
def C : List Nat := [29, 61, 125, 109, 111]
def mask : Nat := 4925626541362553715118340708965721943247706268788170099663654608204315561795786131988558745884852291980005013609060
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
end G025
namespace G026
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 60, 61, 45, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 2]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G169.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G026
namespace G027
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 60, 61, 45, 109]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G171.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G027
namespace G028
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 46, 38, 36, 100]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 4, 3, 1, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    7≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G174.in_snake p P r hr hP
  exact (by decide : 7≤7).trans h
#print axioms in_snake
end G028
namespace G029
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 59, 43, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    16≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G186.in_snake p P r hr hP
  exact (by decide : 16≤16).trans h
#print axioms in_snake
end G029
end Snake9.LocalWindow.FamilyCharge67
