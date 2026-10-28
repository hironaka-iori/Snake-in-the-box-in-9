import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E209
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 111, 103, 231, 227]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 4, 3, 7, 2]
def C : List Nat := [63, 127, 111, 103, 231]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 71, 79, 95, 99, 101, 102, 107, 109, 110, 119, 123, 125, 126, 129, 131, 135, 143, 159, 167, 191, 199, 229, 230, 239, 247, 255, 257, 259, 263, 271, 287, 319, 359, 367, 383, 487]
def D1 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 71, 79, 95, 99, 101, 102, 107, 109, 110, 119, 123, 125, 126, 129, 131, 135, 143, 159, 167, 191, 195, 199, 225, 226, 229, 230, 235, 239, 243, 247, 255, 257, 259, 263, 271, 287, 319, 359, 367, 383, 483, 487]
def mask0 : Nat := 399583814440447005616844445413544988440706481387161084607338628446849645472044783464242611526032815767842685667173382924286391518001378795899742820
def mask1 : Nat := 424557802842974943467897223251890318886695266528480853814211884123852619396793060673886512618159248993486399603260197808951492412864119968958671460
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (163::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (163::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 6 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 6 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=163) (mask0:=mask0) (mask1:=mask1) (L:=6) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E209
