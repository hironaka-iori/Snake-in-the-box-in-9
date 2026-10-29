import CountReject
namespace Snake9.LocalWindow.CountPropagation65.E024
open ForcedShare58 ExtendedShare59 SplitShare62 NeighbourChoice64
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 18, 50, 34, 42]
def dirs : List Nat := [0, 1, 2, 3, 0, 4, 3, 2, 5, 4, 3]
def A : List Nat := [4, 8, 64, 128, 256]
def B : List Nat := [40, 43, 106, 170, 298]
def C : List Nat := [30, 22, 18, 50, 34]
def bounds : List (Nat × Nat) := [(0, 21), (0, 21), (0, 21), (0, 21), (0, 21), (0, 21), (0, 21), (0, 21), (0, 21), (0, 2)]
def c0 : Centre := ⟨14,0,4,0,21⟩
def cond0 : Condition := ofCentre c0
def c1 : Centre := ⟨30,4,3,0,21⟩
def cond1 : Condition := ofCentre c1
def c2 : Centre := ⟨22,3,2,0,21⟩
def cond2 : Condition := ofCentre c2
def c3 : Centre := ⟨18,2,5,0,21⟩
def cond3 : Condition := ofCentre c3
def c4 : Centre := ⟨50,5,4,0,21⟩
def cond4 : Condition := ofCentre c4
def c5 : Centre := ⟨34,4,3,0,2⟩
def cond5 : Condition := ofCentre c5
def centres : List Centre := [c0,c1,c2,c3,c4,c5]
def conds : List Condition := centres.map ofCentre
def cert : Option Nat → Option Nat → TraceCertificate
  | none, none => ⟨[6, 33, 39], [], .upper cond5⟩
  | none, some 40 => ⟨[6, 33, 39], [], .upper cond5⟩
  | none, some 43 => ⟨[6, 33, 39], [], .upper cond5⟩
  | none, some 106 => ⟨[6, 33, 39], [], .upper cond5⟩
  | none, some 170 => ⟨[6, 33, 39], [], .upper cond5⟩
  | none, some 298 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 4, none => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 4, some 40 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 4, some 43 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 4, some 106 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 4, some 170 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 4, some 298 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 8, none => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 8, some 40 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 8, some 43 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 8, some 106 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 8, some 170 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 8, some 298 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 64, none => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 64, some 40 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 64, some 43 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 64, some 106 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 64, some 170 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 64, some 298 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 128, none => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 128, some 40 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 128, some 43 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 128, some 106 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 128, some 170 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 128, some 298 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 256, none => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 256, some 40 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 256, some 43 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 256, some 106 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 256, some 170 => ⟨[6, 33, 39], [], .upper cond5⟩
  | some 256, some 298 => ⟨[6, 33, 39], [], .upper cond5⟩
  | _, _ => ⟨[],[],.share 0⟩
theorem canonical : Canon W dirs := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem centres_checked : centres.all (fun c => (canonicalCentres W dirs bounds).contains c)=true := by decide +kernel
theorem case00 : certCheck W A B C conds 0 (none) (none) (cert (none) (none))=true := by decide +kernel
theorem case01 : certCheck W A B C conds 0 (none) (some 40) (cert (none) (some 40))=true := by decide +kernel
theorem case02 : certCheck W A B C conds 0 (none) (some 43) (cert (none) (some 43))=true := by decide +kernel
theorem case03 : certCheck W A B C conds 0 (none) (some 106) (cert (none) (some 106))=true := by decide +kernel
theorem case04 : certCheck W A B C conds 0 (none) (some 170) (cert (none) (some 170))=true := by decide +kernel
theorem case05 : certCheck W A B C conds 0 (none) (some 298) (cert (none) (some 298))=true := by decide +kernel
theorem case06 : certCheck W A B C conds 0 (some 4) (none) (cert (some 4) (none))=true := by decide +kernel
theorem case07 : certCheck W A B C conds 0 (some 4) (some 40) (cert (some 4) (some 40))=true := by decide +kernel
theorem case08 : certCheck W A B C conds 0 (some 4) (some 43) (cert (some 4) (some 43))=true := by decide +kernel
theorem case09 : certCheck W A B C conds 0 (some 4) (some 106) (cert (some 4) (some 106))=true := by decide +kernel
theorem case10 : certCheck W A B C conds 0 (some 4) (some 170) (cert (some 4) (some 170))=true := by decide +kernel
theorem case11 : certCheck W A B C conds 0 (some 4) (some 298) (cert (some 4) (some 298))=true := by decide +kernel
theorem case12 : certCheck W A B C conds 0 (some 8) (none) (cert (some 8) (none))=true := by decide +kernel
theorem case13 : certCheck W A B C conds 0 (some 8) (some 40) (cert (some 8) (some 40))=true := by decide +kernel
theorem case14 : certCheck W A B C conds 0 (some 8) (some 43) (cert (some 8) (some 43))=true := by decide +kernel
theorem case15 : certCheck W A B C conds 0 (some 8) (some 106) (cert (some 8) (some 106))=true := by decide +kernel
theorem case16 : certCheck W A B C conds 0 (some 8) (some 170) (cert (some 8) (some 170))=true := by decide +kernel
theorem case17 : certCheck W A B C conds 0 (some 8) (some 298) (cert (some 8) (some 298))=true := by decide +kernel
theorem case18 : certCheck W A B C conds 0 (some 64) (none) (cert (some 64) (none))=true := by decide +kernel
theorem case19 : certCheck W A B C conds 0 (some 64) (some 40) (cert (some 64) (some 40))=true := by decide +kernel
theorem case20 : certCheck W A B C conds 0 (some 64) (some 43) (cert (some 64) (some 43))=true := by decide +kernel
theorem case21 : certCheck W A B C conds 0 (some 64) (some 106) (cert (some 64) (some 106))=true := by decide +kernel
theorem case22 : certCheck W A B C conds 0 (some 64) (some 170) (cert (some 64) (some 170))=true := by decide +kernel
theorem case23 : certCheck W A B C conds 0 (some 64) (some 298) (cert (some 64) (some 298))=true := by decide +kernel
theorem case24 : certCheck W A B C conds 0 (some 128) (none) (cert (some 128) (none))=true := by decide +kernel
theorem case25 : certCheck W A B C conds 0 (some 128) (some 40) (cert (some 128) (some 40))=true := by decide +kernel
theorem case26 : certCheck W A B C conds 0 (some 128) (some 43) (cert (some 128) (some 43))=true := by decide +kernel
theorem case27 : certCheck W A B C conds 0 (some 128) (some 106) (cert (some 128) (some 106))=true := by decide +kernel
theorem case28 : certCheck W A B C conds 0 (some 128) (some 170) (cert (some 128) (some 170))=true := by decide +kernel
theorem case29 : certCheck W A B C conds 0 (some 128) (some 298) (cert (some 128) (some 298))=true := by decide +kernel
theorem case30 : certCheck W A B C conds 0 (some 256) (none) (cert (some 256) (none))=true := by decide +kernel
theorem case31 : certCheck W A B C conds 0 (some 256) (some 40) (cert (some 256) (some 40))=true := by decide +kernel
theorem case32 : certCheck W A B C conds 0 (some 256) (some 43) (cert (some 256) (some 43))=true := by decide +kernel
theorem case33 : certCheck W A B C conds 0 (some 256) (some 106) (cert (some 256) (some 106))=true := by decide +kernel
theorem case34 : certCheck W A B C conds 0 (some 256) (some 170) (cert (some 256) (some 170))=true := by decide +kernel
theorem case35 : certCheck W A B C conds 0 (some 256) (some 298) (cert (some 256) (some 298))=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    certCheck W A B C (centres.map ofCentre) 0 a b (cert a b)))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, case05⟩⟩⟩⟩⟩, ⟨⟨case06, ⟨case07, ⟨case08, ⟨case09, ⟨case10, case11⟩⟩⟩⟩⟩, ⟨⟨case12, ⟨case13, ⟨case14, ⟨case15, ⟨case16, case17⟩⟩⟩⟩⟩, ⟨⟨case18, ⟨case19, ⟨case20, ⟨case21, ⟨case22, case23⟩⟩⟩⟩⟩, ⟨⟨case24, ⟨case25, ⟨case26, ⟨case27, ⟨case28, case29⟩⟩⟩⟩⟩, ⟨case30, ⟨case31, ⟨case32, ⟨case33, ⟨case34, case35⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem all_reject : (choices A).all (fun a => (choices B).all (fun b => isRejection (cert a b).ending))=true := by decide +kernel

theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+dirs.length≤m) (hP : ∀ j, j<dirs.length → P.fwd (dir p (r+j))=dirs.getD j 0)
    (hb : ∀ i, i<bounds.length → (bounds.getD i (0,21)).1≤coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1)≤(bounds.getD i (0,21)).2) :
    False := by
  apply count_choices_impossible (W:=W) (dirs:=dirs) (A:=A) (B:=B) (C:=C)
    (bounds:=bounds) (centres:=centres) (start:=6) cert canonical
    (by decide) (by decide) rfl ?_ supported pairA pairB checked all_reject p P r hr hP hb
  intro c hc
  rw [centresOf_canon canonical (by decide)]
  exact List.contains_iff.mp (List.all_eq_true.mp centres_checked c hc)

#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms centres_checked
#print axioms checked
#print axioms all_reject
#print axioms impossible
end Snake9.LocalWindow.CountPropagation65.E024
