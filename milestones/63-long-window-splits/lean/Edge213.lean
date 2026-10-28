import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E213
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 255, 223, 207, 203]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 5, 4, 2]
def C : List Nat := [63, 127, 255, 223, 207]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 71, 79, 95, 111, 119, 123, 125, 126, 129, 131, 135, 143, 159, 191, 199, 205, 206, 215, 219, 221, 222, 239, 247, 251, 253, 254, 257, 259, 263, 271, 287, 319, 383, 463, 479, 511]
def D1 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 71, 75, 79, 95, 111, 119, 123, 125, 126, 129, 131, 135, 139, 143, 159, 191, 199, 201, 202, 205, 206, 215, 219, 221, 222, 235, 239, 247, 251, 253, 254, 257, 259, 263, 271, 287, 319, 383, 459, 463, 479, 511]
def mask0 : Nat := 6703903966532196641996326333240311198898503940401274699921580812896940726092550138827646265106511478112490050943291401798224318575368949114922080848734820
def mask1 : Nat := 6703903966532198130562033690643223043913662495034561056179087500524328182584478060832122292129374371902910807837127858385592836242879618682110673236421220
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (195::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (195::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 4 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 4 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=195) (mask0:=mask0) (mask1:=mask1) (L:=4) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E213
