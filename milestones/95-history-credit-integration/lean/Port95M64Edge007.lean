import Port95M64NeighbourChoice
namespace Snake9.LocalWindow.NeighbourChoice64.E007
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 25, 57, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 1, 5, 0]
def A : List Nat := [8, 16, 32, 64, 128, 256]
def B : List Nat := [40, 48, 60, 120, 184, 312]
def C : List Nat := [30, 26, 27, 25, 57]
def cert : Option Nat → Option Nat → List Nat × Nat
  | none, none => ([9, 10, 11, 12, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | none, some 40 => ([9, 10, 11, 12, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | none, some 48 => ([9, 10, 11, 12, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | none, some 60 => ([9, 10, 11, 12, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | none, some 120 => ([9, 10, 11, 12, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | none, some 184 => ([9, 10, 11, 12, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | none, some 312 => ([9, 10, 11, 12, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 8, none => ([16, 17, 18, 19, 22, 23, 32, 33, 41, 49], 847736363483136)
  | some 8, some 40 => ([12, 16, 17, 18, 19, 22, 23, 28, 32, 33, 44, 48, 49, 60], 1153783534889930752)
  | some 8, some 48 => ([9, 12, 16, 17, 18, 19, 22, 23, 28, 29, 31, 32, 33, 40, 41, 49, 60, 61], 3459330778160108032)
  | some 8, some 60 => ([16, 17, 18, 19, 22, 23, 32, 33, 40, 41, 48, 49], 847736363483136)
  | some 8, some 120 => ([16, 17, 18, 19, 22, 23, 32, 33, 40, 41, 48, 49], 847736363483136)
  | some 8, some 184 => ([16, 17, 18, 19, 22, 23, 32, 33, 40, 41, 48, 49], 847736363483136)
  | some 8, some 312 => ([16, 17, 18, 19, 22, 23, 32, 33, 40, 41, 48, 49], 847736363483136)
  | some 16, none => ([2, 8, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 29, 41], 3299370508036)
  | some 16, some 40 => ([2, 8, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 29, 60, 61], 3458764514656165636)
  | some 16, some 48 => ([2, 4, 8, 9, 10, 11, 12, 15, 17, 18, 19, 20, 22, 23, 24, 28, 41], 2199323057940)
  | some 16, some 60 => ([2, 8, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 29, 40, 41], 3299370508036)
  | some 16, some 120 => ([2, 8, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 29, 40, 41], 3299370508036)
  | some 16, some 184 => ([2, 8, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 29, 40, 41], 3299370508036)
  | some 16, some 312 => ([2, 8, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 29, 40, 41], 3299370508036)
  | some 32, none => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 32, some 40 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 32, some 48 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 32, some 60 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 32, some 120 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 32, some 184 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 32, some 312 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 64, none => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 64, some 40 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 64, some 48 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 64, some 60 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 64, some 120 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 64, some 184 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 64, some 312 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 128, none => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 128, some 40 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 128, some 48 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 128, some 60 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 128, some 120 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 128, some 184 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 128, some 312 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 256, none => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 256, some 40 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 256, some 48 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 256, some 60 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 256, some 120 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 256, some 184 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | some 256, some 312 => ([8, 9, 10, 11, 12, 16, 17, 18, 19, 22, 23, 24, 28], 298786560)
  | _, _ => ([],0)
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem case00 : branchCheck W A B C 18 (none) (none) (cert (none) (none)).1 (cert (none) (none)).2=true := by decide +kernel
theorem case01 : branchCheck W A B C 18 (none) (some 40) (cert (none) (some 40)).1 (cert (none) (some 40)).2=true := by decide +kernel
theorem case02 : branchCheck W A B C 18 (none) (some 48) (cert (none) (some 48)).1 (cert (none) (some 48)).2=true := by decide +kernel
theorem case03 : branchCheck W A B C 18 (none) (some 60) (cert (none) (some 60)).1 (cert (none) (some 60)).2=true := by decide +kernel
theorem case04 : branchCheck W A B C 18 (none) (some 120) (cert (none) (some 120)).1 (cert (none) (some 120)).2=true := by decide +kernel
theorem case05 : branchCheck W A B C 18 (none) (some 184) (cert (none) (some 184)).1 (cert (none) (some 184)).2=true := by decide +kernel
theorem case06 : branchCheck W A B C 18 (none) (some 312) (cert (none) (some 312)).1 (cert (none) (some 312)).2=true := by decide +kernel
theorem case07 : branchCheck W A B C 18 (some 8) (none) (cert (some 8) (none)).1 (cert (some 8) (none)).2=true := by decide +kernel
theorem case08 : branchCheck W A B C 18 (some 8) (some 40) (cert (some 8) (some 40)).1 (cert (some 8) (some 40)).2=true := by decide +kernel
theorem case09 : branchCheck W A B C 18 (some 8) (some 48) (cert (some 8) (some 48)).1 (cert (some 8) (some 48)).2=true := by decide +kernel
theorem case10 : branchCheck W A B C 18 (some 8) (some 60) (cert (some 8) (some 60)).1 (cert (some 8) (some 60)).2=true := by decide +kernel
theorem case11 : branchCheck W A B C 18 (some 8) (some 120) (cert (some 8) (some 120)).1 (cert (some 8) (some 120)).2=true := by decide +kernel
theorem case12 : branchCheck W A B C 18 (some 8) (some 184) (cert (some 8) (some 184)).1 (cert (some 8) (some 184)).2=true := by decide +kernel
theorem case13 : branchCheck W A B C 18 (some 8) (some 312) (cert (some 8) (some 312)).1 (cert (some 8) (some 312)).2=true := by decide +kernel
theorem case14 : branchCheck W A B C 18 (some 16) (none) (cert (some 16) (none)).1 (cert (some 16) (none)).2=true := by decide +kernel
theorem case15 : branchCheck W A B C 18 (some 16) (some 40) (cert (some 16) (some 40)).1 (cert (some 16) (some 40)).2=true := by decide +kernel
theorem case16 : branchCheck W A B C 18 (some 16) (some 48) (cert (some 16) (some 48)).1 (cert (some 16) (some 48)).2=true := by decide +kernel
theorem case17 : branchCheck W A B C 18 (some 16) (some 60) (cert (some 16) (some 60)).1 (cert (some 16) (some 60)).2=true := by decide +kernel
theorem case18 : branchCheck W A B C 18 (some 16) (some 120) (cert (some 16) (some 120)).1 (cert (some 16) (some 120)).2=true := by decide +kernel
theorem case19 : branchCheck W A B C 18 (some 16) (some 184) (cert (some 16) (some 184)).1 (cert (some 16) (some 184)).2=true := by decide +kernel
theorem case20 : branchCheck W A B C 18 (some 16) (some 312) (cert (some 16) (some 312)).1 (cert (some 16) (some 312)).2=true := by decide +kernel
theorem case21 : branchCheck W A B C 18 (some 32) (none) (cert (some 32) (none)).1 (cert (some 32) (none)).2=true := by decide +kernel
theorem case22 : branchCheck W A B C 18 (some 32) (some 40) (cert (some 32) (some 40)).1 (cert (some 32) (some 40)).2=true := by decide +kernel
theorem case23 : branchCheck W A B C 18 (some 32) (some 48) (cert (some 32) (some 48)).1 (cert (some 32) (some 48)).2=true := by decide +kernel
theorem case24 : branchCheck W A B C 18 (some 32) (some 60) (cert (some 32) (some 60)).1 (cert (some 32) (some 60)).2=true := by decide +kernel
theorem case25 : branchCheck W A B C 18 (some 32) (some 120) (cert (some 32) (some 120)).1 (cert (some 32) (some 120)).2=true := by decide +kernel
theorem case26 : branchCheck W A B C 18 (some 32) (some 184) (cert (some 32) (some 184)).1 (cert (some 32) (some 184)).2=true := by decide +kernel
theorem case27 : branchCheck W A B C 18 (some 32) (some 312) (cert (some 32) (some 312)).1 (cert (some 32) (some 312)).2=true := by decide +kernel
theorem case28 : branchCheck W A B C 18 (some 64) (none) (cert (some 64) (none)).1 (cert (some 64) (none)).2=true := by decide +kernel
theorem case29 : branchCheck W A B C 18 (some 64) (some 40) (cert (some 64) (some 40)).1 (cert (some 64) (some 40)).2=true := by decide +kernel
theorem case30 : branchCheck W A B C 18 (some 64) (some 48) (cert (some 64) (some 48)).1 (cert (some 64) (some 48)).2=true := by decide +kernel
theorem case31 : branchCheck W A B C 18 (some 64) (some 60) (cert (some 64) (some 60)).1 (cert (some 64) (some 60)).2=true := by decide +kernel
theorem case32 : branchCheck W A B C 18 (some 64) (some 120) (cert (some 64) (some 120)).1 (cert (some 64) (some 120)).2=true := by decide +kernel
theorem case33 : branchCheck W A B C 18 (some 64) (some 184) (cert (some 64) (some 184)).1 (cert (some 64) (some 184)).2=true := by decide +kernel
theorem case34 : branchCheck W A B C 18 (some 64) (some 312) (cert (some 64) (some 312)).1 (cert (some 64) (some 312)).2=true := by decide +kernel
theorem case35 : branchCheck W A B C 18 (some 128) (none) (cert (some 128) (none)).1 (cert (some 128) (none)).2=true := by decide +kernel
theorem case36 : branchCheck W A B C 18 (some 128) (some 40) (cert (some 128) (some 40)).1 (cert (some 128) (some 40)).2=true := by decide +kernel
theorem case37 : branchCheck W A B C 18 (some 128) (some 48) (cert (some 128) (some 48)).1 (cert (some 128) (some 48)).2=true := by decide +kernel
theorem case38 : branchCheck W A B C 18 (some 128) (some 60) (cert (some 128) (some 60)).1 (cert (some 128) (some 60)).2=true := by decide +kernel
theorem case39 : branchCheck W A B C 18 (some 128) (some 120) (cert (some 128) (some 120)).1 (cert (some 128) (some 120)).2=true := by decide +kernel
theorem case40 : branchCheck W A B C 18 (some 128) (some 184) (cert (some 128) (some 184)).1 (cert (some 128) (some 184)).2=true := by decide +kernel
theorem case41 : branchCheck W A B C 18 (some 128) (some 312) (cert (some 128) (some 312)).1 (cert (some 128) (some 312)).2=true := by decide +kernel
theorem case42 : branchCheck W A B C 18 (some 256) (none) (cert (some 256) (none)).1 (cert (some 256) (none)).2=true := by decide +kernel
theorem case43 : branchCheck W A B C 18 (some 256) (some 40) (cert (some 256) (some 40)).1 (cert (some 256) (some 40)).2=true := by decide +kernel
theorem case44 : branchCheck W A B C 18 (some 256) (some 48) (cert (some 256) (some 48)).1 (cert (some 256) (some 48)).2=true := by decide +kernel
theorem case45 : branchCheck W A B C 18 (some 256) (some 60) (cert (some 256) (some 60)).1 (cert (some 256) (some 60)).2=true := by decide +kernel
theorem case46 : branchCheck W A B C 18 (some 256) (some 120) (cert (some 256) (some 120)).1 (cert (some 256) (some 120)).2=true := by decide +kernel
theorem case47 : branchCheck W A B C 18 (some 256) (some 184) (cert (some 256) (some 184)).1 (cert (some 256) (some 184)).2=true := by decide +kernel
theorem case48 : branchCheck W A B C 18 (some 256) (some 312) (cert (some 256) (some 312)).1 (cert (some 256) (some 312)).2=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    branchCheck W A B C 18 a b (cert a b).1 (cert a b).2))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, ⟨case05, case06⟩⟩⟩⟩⟩⟩, ⟨⟨case07, ⟨case08, ⟨case09, ⟨case10, ⟨case11, ⟨case12, case13⟩⟩⟩⟩⟩⟩, ⟨⟨case14, ⟨case15, ⟨case16, ⟨case17, ⟨case18, ⟨case19, case20⟩⟩⟩⟩⟩⟩, ⟨⟨case21, ⟨case22, ⟨case23, ⟨case24, ⟨case25, ⟨case26, case27⟩⟩⟩⟩⟩⟩, ⟨⟨case28, ⟨case29, ⟨case30, ⟨case31, ⟨case32, ⟨case33, case34⟩⟩⟩⟩⟩⟩, ⟨⟨case35, ⟨case36, ⟨case37, ⟨case38, ⟨case39, ⟨case40, case41⟩⟩⟩⟩⟩⟩, ⟨case42, ⟨case43, ⟨case44, ⟨case45, ⟨case46, ⟨case47, case48⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    18≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  neighbour_in_snake (W:=W) (cs:=ds) (A:=A) (B:=B) (C:=C) (L:=18) (start:=6)
    cert canonical (by decide) (by decide) rfl supported pairA pairB checked p P r hr hP
#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.NeighbourChoice64.E007
