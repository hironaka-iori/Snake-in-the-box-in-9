import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E189
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 126, 94, 78, 74]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 0, 5, 4, 2]
def C : List Nat := [63, 127, 126, 94, 78]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 70, 71, 76, 79, 86, 90, 92, 95, 110, 111, 118, 119, 122, 123, 124, 125, 129, 131, 135, 143, 159, 191, 206, 222, 254, 255, 257, 259, 263, 271, 287, 319, 334, 350, 382, 383]
def D1 : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 70, 71, 72, 75, 76, 79, 86, 90, 92, 95, 106, 110, 111, 118, 119, 122, 123, 124, 125, 129, 131, 135, 143, 159, 191, 202, 206, 222, 254, 255, 257, 259, 263, 271, 287, 319, 330, 334, 350, 382, 383]
def mask0 : Nat := 29551504649589393022278941633118441678891261959811416666323630127582697682159120436665079307260004307495442386152036
def mask1 : Nat := 29551504649589395209529666416130366051393489077432782025920813197831095210097575216063858555181773699205111724273252
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (66::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (66::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 4 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 4 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=66) (mask0:=mask0) (mask1:=mask1) (L:=4) (start:=6)
    canonical (by decide) (by decide) rfl forced0 forced1 supported
    checked_mask0 checked_mask1 credit0 credit1 p P r hr hP
#print axioms canonical
#print axioms forced0
#print axioms forced1
#print axioms supported
#print axioms checked_mask0
#print axioms checked_mask1
#print axioms credit0
#print axioms credit1
#print axioms in_snake
end Snake9.LocalWindow.LongWindow63.E189
