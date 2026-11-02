import Port95M64NeighbourChoice
namespace Snake9.LocalWindow.NeighbourChoice64.E010
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 53, 52]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 1, 0]
def A : List Nat := [8, 16, 32, 64, 128, 256]
def B : List Nat := [20, 36, 48, 116, 180, 308]
def C : List Nat := [30, 62, 63, 55, 53]
def cert : Option Nat → Option Nat → List Nat × Nat
  | none, none => ([4, 5, 12, 15, 17, 19, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47], 212180259278896)
  | none, some 20 => ([4, 5, 15, 17, 19, 21, 22, 23, 33, 35, 36, 37, 38, 39, 46, 47, 48, 49, 51], 3308404733607984)
  | none, some 36 => ([4, 5, 12, 15, 17, 19, 20, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47, 49, 51], 3026861306908720)
  | none, some 48 => ([4, 5, 12, 15, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | none, some 116 => ([4, 5, 12, 15, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | none, some 180 => ([4, 5, 12, 15, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | none, some 308 => ([4, 5, 12, 15, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 8, none => ([4, 5, 12, 15, 16, 17, 19, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47], 212180259278896)
  | some 8, some 20 => ([4, 5, 15, 16, 17, 19, 21, 22, 23, 33, 35, 36, 37, 38, 39, 46, 47, 48, 49, 51], 3308404733607984)
  | some 8, some 36 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47, 49, 51], 3026861306908720)
  | some 8, some 48 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 8, some 116 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 8, some 180 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 8, some 308 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 16, none => ([4, 5, 12, 15, 17, 19, 21, 22, 23, 28, 32, 33, 35, 37, 38, 39, 46, 47], 212184554180656)
  | some 16, some 20 => ([2, 4, 5, 8, 10, 15, 17, 18, 19, 21, 22, 23, 24, 26, 32, 33, 35, 36, 37, 38, 39, 46, 47, 48, 49], 1056609298974004)
  | some 16, some 36 => ([4, 5, 15, 17, 19, 20, 21, 22, 23, 32, 33, 35, 37, 38, 39, 46, 47, 48, 49, 51], 3308340310081584)
  | some 16, some 48 => ([2, 4, 5, 8, 10, 12, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 32, 33, 35, 36, 37, 39], 803527857460)
  | some 16, some 116 => ([4, 5, 12, 15, 17, 19, 20, 21, 22, 23, 28, 32, 33, 35, 36, 37, 38, 39, 46, 47], 212184554180656)
  | some 16, some 180 => ([4, 5, 12, 15, 17, 19, 20, 21, 22, 23, 28, 32, 33, 35, 36, 37, 38, 39, 46, 47], 212184554180656)
  | some 16, some 308 => ([4, 5, 12, 15, 17, 19, 20, 21, 22, 23, 28, 32, 33, 35, 36, 37, 38, 39, 46, 47], 212184554180656)
  | some 32, none => ([4, 5, 12, 15, 16, 17, 19, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47], 212180259278896)
  | some 32, some 20 => ([4, 5, 15, 16, 17, 19, 21, 22, 23, 33, 35, 36, 37, 38, 39, 46, 47, 48, 49, 51], 3308404733607984)
  | some 32, some 36 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47, 49, 51], 3026861306908720)
  | some 32, some 48 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 32, some 116 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 32, some 180 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 32, some 308 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 64, none => ([4, 5, 12, 15, 16, 17, 19, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47], 212180259278896)
  | some 64, some 20 => ([4, 5, 15, 16, 17, 19, 21, 22, 23, 33, 35, 36, 37, 38, 39, 46, 47, 48, 49, 51], 3308404733607984)
  | some 64, some 36 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47, 49, 51], 3026861306908720)
  | some 64, some 48 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 64, some 116 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 64, some 180 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 64, some 308 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 128, none => ([4, 5, 12, 15, 16, 17, 19, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47], 212180259278896)
  | some 128, some 20 => ([4, 5, 15, 16, 17, 19, 21, 22, 23, 33, 35, 36, 37, 38, 39, 46, 47, 48, 49, 51], 3308404733607984)
  | some 128, some 36 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47, 49, 51], 3026861306908720)
  | some 128, some 48 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 128, some 116 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 128, some 180 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 128, some 308 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 256, none => ([4, 5, 12, 15, 16, 17, 19, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47], 212180259278896)
  | some 256, some 20 => ([4, 5, 15, 16, 17, 19, 21, 22, 23, 33, 35, 36, 37, 38, 39, 46, 47, 48, 49, 51], 3308404733607984)
  | some 256, some 36 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 37, 38, 39, 46, 47, 49, 51], 3026861306908720)
  | some 256, some 48 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 256, some 116 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 256, some 180 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | some 256, some 308 => ([4, 5, 12, 15, 16, 17, 19, 20, 21, 22, 23, 28, 33, 35, 36, 37, 38, 39, 46, 47], 212180259278896)
  | _, _ => ([],0)
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem case00 : branchCheck W A B C 32 (none) (none) (cert (none) (none)).1 (cert (none) (none)).2=true := by decide +kernel
theorem case01 : branchCheck W A B C 32 (none) (some 20) (cert (none) (some 20)).1 (cert (none) (some 20)).2=true := by decide +kernel
theorem case02 : branchCheck W A B C 32 (none) (some 36) (cert (none) (some 36)).1 (cert (none) (some 36)).2=true := by decide +kernel
theorem case03 : branchCheck W A B C 32 (none) (some 48) (cert (none) (some 48)).1 (cert (none) (some 48)).2=true := by decide +kernel
theorem case04 : branchCheck W A B C 32 (none) (some 116) (cert (none) (some 116)).1 (cert (none) (some 116)).2=true := by decide +kernel
theorem case05 : branchCheck W A B C 32 (none) (some 180) (cert (none) (some 180)).1 (cert (none) (some 180)).2=true := by decide +kernel
theorem case06 : branchCheck W A B C 32 (none) (some 308) (cert (none) (some 308)).1 (cert (none) (some 308)).2=true := by decide +kernel
theorem case07 : branchCheck W A B C 32 (some 8) (none) (cert (some 8) (none)).1 (cert (some 8) (none)).2=true := by decide +kernel
theorem case08 : branchCheck W A B C 32 (some 8) (some 20) (cert (some 8) (some 20)).1 (cert (some 8) (some 20)).2=true := by decide +kernel
theorem case09 : branchCheck W A B C 32 (some 8) (some 36) (cert (some 8) (some 36)).1 (cert (some 8) (some 36)).2=true := by decide +kernel
theorem case10 : branchCheck W A B C 32 (some 8) (some 48) (cert (some 8) (some 48)).1 (cert (some 8) (some 48)).2=true := by decide +kernel
theorem case11 : branchCheck W A B C 32 (some 8) (some 116) (cert (some 8) (some 116)).1 (cert (some 8) (some 116)).2=true := by decide +kernel
theorem case12 : branchCheck W A B C 32 (some 8) (some 180) (cert (some 8) (some 180)).1 (cert (some 8) (some 180)).2=true := by decide +kernel
theorem case13 : branchCheck W A B C 32 (some 8) (some 308) (cert (some 8) (some 308)).1 (cert (some 8) (some 308)).2=true := by decide +kernel
theorem case14 : branchCheck W A B C 32 (some 16) (none) (cert (some 16) (none)).1 (cert (some 16) (none)).2=true := by decide +kernel
theorem case15 : branchCheck W A B C 32 (some 16) (some 20) (cert (some 16) (some 20)).1 (cert (some 16) (some 20)).2=true := by decide +kernel
theorem case16 : branchCheck W A B C 32 (some 16) (some 36) (cert (some 16) (some 36)).1 (cert (some 16) (some 36)).2=true := by decide +kernel
theorem case17 : branchCheck W A B C 32 (some 16) (some 48) (cert (some 16) (some 48)).1 (cert (some 16) (some 48)).2=true := by decide +kernel
theorem case18 : branchCheck W A B C 32 (some 16) (some 116) (cert (some 16) (some 116)).1 (cert (some 16) (some 116)).2=true := by decide +kernel
theorem case19 : branchCheck W A B C 32 (some 16) (some 180) (cert (some 16) (some 180)).1 (cert (some 16) (some 180)).2=true := by decide +kernel
theorem case20 : branchCheck W A B C 32 (some 16) (some 308) (cert (some 16) (some 308)).1 (cert (some 16) (some 308)).2=true := by decide +kernel
theorem case21 : branchCheck W A B C 32 (some 32) (none) (cert (some 32) (none)).1 (cert (some 32) (none)).2=true := by decide +kernel
theorem case22 : branchCheck W A B C 32 (some 32) (some 20) (cert (some 32) (some 20)).1 (cert (some 32) (some 20)).2=true := by decide +kernel
theorem case23 : branchCheck W A B C 32 (some 32) (some 36) (cert (some 32) (some 36)).1 (cert (some 32) (some 36)).2=true := by decide +kernel
theorem case24 : branchCheck W A B C 32 (some 32) (some 48) (cert (some 32) (some 48)).1 (cert (some 32) (some 48)).2=true := by decide +kernel
theorem case25 : branchCheck W A B C 32 (some 32) (some 116) (cert (some 32) (some 116)).1 (cert (some 32) (some 116)).2=true := by decide +kernel
theorem case26 : branchCheck W A B C 32 (some 32) (some 180) (cert (some 32) (some 180)).1 (cert (some 32) (some 180)).2=true := by decide +kernel
theorem case27 : branchCheck W A B C 32 (some 32) (some 308) (cert (some 32) (some 308)).1 (cert (some 32) (some 308)).2=true := by decide +kernel
theorem case28 : branchCheck W A B C 32 (some 64) (none) (cert (some 64) (none)).1 (cert (some 64) (none)).2=true := by decide +kernel
theorem case29 : branchCheck W A B C 32 (some 64) (some 20) (cert (some 64) (some 20)).1 (cert (some 64) (some 20)).2=true := by decide +kernel
theorem case30 : branchCheck W A B C 32 (some 64) (some 36) (cert (some 64) (some 36)).1 (cert (some 64) (some 36)).2=true := by decide +kernel
theorem case31 : branchCheck W A B C 32 (some 64) (some 48) (cert (some 64) (some 48)).1 (cert (some 64) (some 48)).2=true := by decide +kernel
theorem case32 : branchCheck W A B C 32 (some 64) (some 116) (cert (some 64) (some 116)).1 (cert (some 64) (some 116)).2=true := by decide +kernel
theorem case33 : branchCheck W A B C 32 (some 64) (some 180) (cert (some 64) (some 180)).1 (cert (some 64) (some 180)).2=true := by decide +kernel
theorem case34 : branchCheck W A B C 32 (some 64) (some 308) (cert (some 64) (some 308)).1 (cert (some 64) (some 308)).2=true := by decide +kernel
theorem case35 : branchCheck W A B C 32 (some 128) (none) (cert (some 128) (none)).1 (cert (some 128) (none)).2=true := by decide +kernel
theorem case36 : branchCheck W A B C 32 (some 128) (some 20) (cert (some 128) (some 20)).1 (cert (some 128) (some 20)).2=true := by decide +kernel
theorem case37 : branchCheck W A B C 32 (some 128) (some 36) (cert (some 128) (some 36)).1 (cert (some 128) (some 36)).2=true := by decide +kernel
theorem case38 : branchCheck W A B C 32 (some 128) (some 48) (cert (some 128) (some 48)).1 (cert (some 128) (some 48)).2=true := by decide +kernel
theorem case39 : branchCheck W A B C 32 (some 128) (some 116) (cert (some 128) (some 116)).1 (cert (some 128) (some 116)).2=true := by decide +kernel
theorem case40 : branchCheck W A B C 32 (some 128) (some 180) (cert (some 128) (some 180)).1 (cert (some 128) (some 180)).2=true := by decide +kernel
theorem case41 : branchCheck W A B C 32 (some 128) (some 308) (cert (some 128) (some 308)).1 (cert (some 128) (some 308)).2=true := by decide +kernel
theorem case42 : branchCheck W A B C 32 (some 256) (none) (cert (some 256) (none)).1 (cert (some 256) (none)).2=true := by decide +kernel
theorem case43 : branchCheck W A B C 32 (some 256) (some 20) (cert (some 256) (some 20)).1 (cert (some 256) (some 20)).2=true := by decide +kernel
theorem case44 : branchCheck W A B C 32 (some 256) (some 36) (cert (some 256) (some 36)).1 (cert (some 256) (some 36)).2=true := by decide +kernel
theorem case45 : branchCheck W A B C 32 (some 256) (some 48) (cert (some 256) (some 48)).1 (cert (some 256) (some 48)).2=true := by decide +kernel
theorem case46 : branchCheck W A B C 32 (some 256) (some 116) (cert (some 256) (some 116)).1 (cert (some 256) (some 116)).2=true := by decide +kernel
theorem case47 : branchCheck W A B C 32 (some 256) (some 180) (cert (some 256) (some 180)).1 (cert (some 256) (some 180)).2=true := by decide +kernel
theorem case48 : branchCheck W A B C 32 (some 256) (some 308) (cert (some 256) (some 308)).1 (cert (some 256) (some 308)).2=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    branchCheck W A B C 32 a b (cert a b).1 (cert a b).2))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, ⟨case05, case06⟩⟩⟩⟩⟩⟩, ⟨⟨case07, ⟨case08, ⟨case09, ⟨case10, ⟨case11, ⟨case12, case13⟩⟩⟩⟩⟩⟩, ⟨⟨case14, ⟨case15, ⟨case16, ⟨case17, ⟨case18, ⟨case19, case20⟩⟩⟩⟩⟩⟩, ⟨⟨case21, ⟨case22, ⟨case23, ⟨case24, ⟨case25, ⟨case26, case27⟩⟩⟩⟩⟩⟩, ⟨⟨case28, ⟨case29, ⟨case30, ⟨case31, ⟨case32, ⟨case33, case34⟩⟩⟩⟩⟩⟩, ⟨⟨case35, ⟨case36, ⟨case37, ⟨case38, ⟨case39, ⟨case40, case41⟩⟩⟩⟩⟩⟩, ⟨case42, ⟨case43, ⟨case44, ⟨case45, ⟨case46, ⟨case47, case48⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    32≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  neighbour_in_snake (W:=W) (cs:=ds) (A:=A) (B:=B) (C:=C) (L:=32) (start:=6)
    cert canonical (by decide) (by decide) rfl supported pairA pairB checked p P r hr hP
#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.NeighbourChoice64.E010
