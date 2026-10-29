import NeighbourChoice
namespace Snake9.LocalWindow.NeighbourChoice64.E195
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 125, 93, 77, 76]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 0]
def A : List Nat := [4, 8, 16, 32, 64, 128, 256]
def B : List Nat := [12, 68, 72, 78, 108, 204, 332]
def C : List Nat := [63, 127, 125, 93, 77]
def cert : Option Nat → Option Nat → List Nat × Nat
  | none, none => ([5, 9, 13, 65, 69], 922337203685477593904)
  | none, some 12 => ([5, 65, 67, 68, 69, 71], 3449541141783686152240)
  | none, some 68 => ([5, 9, 12, 13, 65, 67, 69, 71], 3135946492530623787824)
  | none, some 72 => ([5, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | none, some 78 => ([5, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | none, some 108 => ([5, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | none, some 204 => ([5, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | none, some 332 => ([5, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 4, none => ([5, 8, 9, 13, 64, 65, 67, 69, 71], 3449541141783686165280)
  | some 4, some 12 => ([5, 8, 9, 64, 65, 68, 69, 72, 73], 15107883396368122774304)
  | some 4, some 68 => ([5, 8, 9, 12, 13, 64, 65, 72, 73], 14222439680830064309024)
  | some 4, some 72 => ([5, 8, 9, 12, 13, 64, 65, 67, 68, 69, 71], 3449541141783686165280)
  | some 4, some 78 => ([5, 8, 9, 12, 13, 64, 65, 67, 68, 69, 71], 3449541141783686165280)
  | some 4, some 108 => ([5, 8, 9, 12, 13, 64, 65, 67, 68, 69, 71], 3449541141783686165280)
  | some 4, some 204 => ([5, 8, 9, 12, 13, 64, 65, 67, 68, 69, 71], 3449541141783686165280)
  | some 4, some 332 => ([5, 8, 9, 12, 13, 64, 65, 67, 68, 69, 71], 3449541141783686165280)
  | some 8, none => ([4, 5, 9, 13, 64, 65, 69], 940783947759187145264)
  | some 8, some 12 => ([4, 5, 64, 65, 67, 68, 69, 71], 3449541141783686152240)
  | some 8, some 68 => ([4, 5, 9, 12, 13, 64, 65, 67, 69, 71, 72, 73], 17321492685213268980272)
  | some 8, some 72 => ([4, 5, 9, 12, 13, 64, 65, 68, 69], 940783947759187145264)
  | some 8, some 78 => ([4, 5, 9, 12, 13, 64, 65, 68, 69], 940783947759187145264)
  | some 8, some 108 => ([4, 5, 9, 12, 13, 64, 65, 68, 69], 940783947759187145264)
  | some 8, some 204 => ([4, 5, 9, 12, 13, 64, 65, 68, 69], 940783947759187145264)
  | some 8, some 332 => ([4, 5, 9, 12, 13, 64, 65, 68, 69], 940783947759187145264)
  | some 16, none => ([4, 5, 8, 9, 13, 65, 69], 922337203685477593904)
  | some 16, some 12 => ([4, 5, 64, 65, 67, 68, 69, 71], 3449541141783686152240)
  | some 16, some 68 => ([4, 5, 8, 9, 12, 13, 65, 67, 69, 71], 3135946492530623787824)
  | some 16, some 72 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 16, some 78 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 16, some 108 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 16, some 204 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 16, some 332 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 32, none => ([4, 5, 8, 9, 13, 65, 69], 922337203685477593904)
  | some 32, some 12 => ([4, 5, 64, 65, 67, 68, 69, 71], 3449541141783686152240)
  | some 32, some 68 => ([4, 5, 8, 9, 12, 13, 65, 67, 69, 71], 3135946492530623787824)
  | some 32, some 72 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 32, some 78 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 32, some 108 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 32, some 204 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 32, some 332 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 64, none => ([4, 5, 8, 9, 13, 65, 69], 922337203685477593904)
  | some 64, some 12 => ([4, 5, 8, 9, 65, 67, 68, 69, 71, 72, 73], 17598193846318912242480)
  | some 64, some 68 => ([4, 5, 8, 9, 12, 13, 65, 67, 69, 71], 3135946492530623787824)
  | some 64, some 72 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 64, some 78 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 64, some 108 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 64, some 204 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 64, some 332 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 128, none => ([4, 5, 8, 9, 13, 65, 69], 922337203685477593904)
  | some 128, some 12 => ([4, 5, 64, 65, 67, 68, 69, 71], 3449541141783686152240)
  | some 128, some 68 => ([4, 5, 8, 9, 12, 13, 65, 67, 69, 71], 3135946492530623787824)
  | some 128, some 72 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 128, some 78 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 128, some 108 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 128, some 204 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 128, some 332 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 256, none => ([4, 5, 8, 9, 13, 65, 69], 922337203685477593904)
  | some 256, some 12 => ([4, 5, 64, 65, 67, 68, 69, 71], 3449541141783686152240)
  | some 256, some 68 => ([4, 5, 8, 9, 12, 13, 65, 67, 69, 71], 3135946492530623787824)
  | some 256, some 72 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 256, some 78 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 256, some 108 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 256, some 204 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | some 256, some 332 => ([4, 5, 8, 9, 12, 13, 65, 68, 69], 922337203685477593904)
  | _, _ => ([],0)
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem case00 : branchCheck W A B C 6 (none) (none) (cert (none) (none)).1 (cert (none) (none)).2=true := by decide +kernel
theorem case01 : branchCheck W A B C 6 (none) (some 12) (cert (none) (some 12)).1 (cert (none) (some 12)).2=true := by decide +kernel
theorem case02 : branchCheck W A B C 6 (none) (some 68) (cert (none) (some 68)).1 (cert (none) (some 68)).2=true := by decide +kernel
theorem case03 : branchCheck W A B C 6 (none) (some 72) (cert (none) (some 72)).1 (cert (none) (some 72)).2=true := by decide +kernel
theorem case04 : branchCheck W A B C 6 (none) (some 78) (cert (none) (some 78)).1 (cert (none) (some 78)).2=true := by decide +kernel
theorem case05 : branchCheck W A B C 6 (none) (some 108) (cert (none) (some 108)).1 (cert (none) (some 108)).2=true := by decide +kernel
theorem case06 : branchCheck W A B C 6 (none) (some 204) (cert (none) (some 204)).1 (cert (none) (some 204)).2=true := by decide +kernel
theorem case07 : branchCheck W A B C 6 (none) (some 332) (cert (none) (some 332)).1 (cert (none) (some 332)).2=true := by decide +kernel
theorem case08 : branchCheck W A B C 6 (some 4) (none) (cert (some 4) (none)).1 (cert (some 4) (none)).2=true := by decide +kernel
theorem case09 : branchCheck W A B C 6 (some 4) (some 12) (cert (some 4) (some 12)).1 (cert (some 4) (some 12)).2=true := by decide +kernel
theorem case10 : branchCheck W A B C 6 (some 4) (some 68) (cert (some 4) (some 68)).1 (cert (some 4) (some 68)).2=true := by decide +kernel
theorem case11 : branchCheck W A B C 6 (some 4) (some 72) (cert (some 4) (some 72)).1 (cert (some 4) (some 72)).2=true := by decide +kernel
theorem case12 : branchCheck W A B C 6 (some 4) (some 78) (cert (some 4) (some 78)).1 (cert (some 4) (some 78)).2=true := by decide +kernel
theorem case13 : branchCheck W A B C 6 (some 4) (some 108) (cert (some 4) (some 108)).1 (cert (some 4) (some 108)).2=true := by decide +kernel
theorem case14 : branchCheck W A B C 6 (some 4) (some 204) (cert (some 4) (some 204)).1 (cert (some 4) (some 204)).2=true := by decide +kernel
theorem case15 : branchCheck W A B C 6 (some 4) (some 332) (cert (some 4) (some 332)).1 (cert (some 4) (some 332)).2=true := by decide +kernel
theorem case16 : branchCheck W A B C 6 (some 8) (none) (cert (some 8) (none)).1 (cert (some 8) (none)).2=true := by decide +kernel
theorem case17 : branchCheck W A B C 6 (some 8) (some 12) (cert (some 8) (some 12)).1 (cert (some 8) (some 12)).2=true := by decide +kernel
theorem case18 : branchCheck W A B C 6 (some 8) (some 68) (cert (some 8) (some 68)).1 (cert (some 8) (some 68)).2=true := by decide +kernel
theorem case19 : branchCheck W A B C 6 (some 8) (some 72) (cert (some 8) (some 72)).1 (cert (some 8) (some 72)).2=true := by decide +kernel
theorem case20 : branchCheck W A B C 6 (some 8) (some 78) (cert (some 8) (some 78)).1 (cert (some 8) (some 78)).2=true := by decide +kernel
theorem case21 : branchCheck W A B C 6 (some 8) (some 108) (cert (some 8) (some 108)).1 (cert (some 8) (some 108)).2=true := by decide +kernel
theorem case22 : branchCheck W A B C 6 (some 8) (some 204) (cert (some 8) (some 204)).1 (cert (some 8) (some 204)).2=true := by decide +kernel
theorem case23 : branchCheck W A B C 6 (some 8) (some 332) (cert (some 8) (some 332)).1 (cert (some 8) (some 332)).2=true := by decide +kernel
theorem case24 : branchCheck W A B C 6 (some 16) (none) (cert (some 16) (none)).1 (cert (some 16) (none)).2=true := by decide +kernel
theorem case25 : branchCheck W A B C 6 (some 16) (some 12) (cert (some 16) (some 12)).1 (cert (some 16) (some 12)).2=true := by decide +kernel
theorem case26 : branchCheck W A B C 6 (some 16) (some 68) (cert (some 16) (some 68)).1 (cert (some 16) (some 68)).2=true := by decide +kernel
theorem case27 : branchCheck W A B C 6 (some 16) (some 72) (cert (some 16) (some 72)).1 (cert (some 16) (some 72)).2=true := by decide +kernel
theorem case28 : branchCheck W A B C 6 (some 16) (some 78) (cert (some 16) (some 78)).1 (cert (some 16) (some 78)).2=true := by decide +kernel
theorem case29 : branchCheck W A B C 6 (some 16) (some 108) (cert (some 16) (some 108)).1 (cert (some 16) (some 108)).2=true := by decide +kernel
theorem case30 : branchCheck W A B C 6 (some 16) (some 204) (cert (some 16) (some 204)).1 (cert (some 16) (some 204)).2=true := by decide +kernel
theorem case31 : branchCheck W A B C 6 (some 16) (some 332) (cert (some 16) (some 332)).1 (cert (some 16) (some 332)).2=true := by decide +kernel
theorem case32 : branchCheck W A B C 6 (some 32) (none) (cert (some 32) (none)).1 (cert (some 32) (none)).2=true := by decide +kernel
theorem case33 : branchCheck W A B C 6 (some 32) (some 12) (cert (some 32) (some 12)).1 (cert (some 32) (some 12)).2=true := by decide +kernel
theorem case34 : branchCheck W A B C 6 (some 32) (some 68) (cert (some 32) (some 68)).1 (cert (some 32) (some 68)).2=true := by decide +kernel
theorem case35 : branchCheck W A B C 6 (some 32) (some 72) (cert (some 32) (some 72)).1 (cert (some 32) (some 72)).2=true := by decide +kernel
theorem case36 : branchCheck W A B C 6 (some 32) (some 78) (cert (some 32) (some 78)).1 (cert (some 32) (some 78)).2=true := by decide +kernel
theorem case37 : branchCheck W A B C 6 (some 32) (some 108) (cert (some 32) (some 108)).1 (cert (some 32) (some 108)).2=true := by decide +kernel
theorem case38 : branchCheck W A B C 6 (some 32) (some 204) (cert (some 32) (some 204)).1 (cert (some 32) (some 204)).2=true := by decide +kernel
theorem case39 : branchCheck W A B C 6 (some 32) (some 332) (cert (some 32) (some 332)).1 (cert (some 32) (some 332)).2=true := by decide +kernel
theorem case40 : branchCheck W A B C 6 (some 64) (none) (cert (some 64) (none)).1 (cert (some 64) (none)).2=true := by decide +kernel
theorem case41 : branchCheck W A B C 6 (some 64) (some 12) (cert (some 64) (some 12)).1 (cert (some 64) (some 12)).2=true := by decide +kernel
theorem case42 : branchCheck W A B C 6 (some 64) (some 68) (cert (some 64) (some 68)).1 (cert (some 64) (some 68)).2=true := by decide +kernel
theorem case43 : branchCheck W A B C 6 (some 64) (some 72) (cert (some 64) (some 72)).1 (cert (some 64) (some 72)).2=true := by decide +kernel
theorem case44 : branchCheck W A B C 6 (some 64) (some 78) (cert (some 64) (some 78)).1 (cert (some 64) (some 78)).2=true := by decide +kernel
theorem case45 : branchCheck W A B C 6 (some 64) (some 108) (cert (some 64) (some 108)).1 (cert (some 64) (some 108)).2=true := by decide +kernel
theorem case46 : branchCheck W A B C 6 (some 64) (some 204) (cert (some 64) (some 204)).1 (cert (some 64) (some 204)).2=true := by decide +kernel
theorem case47 : branchCheck W A B C 6 (some 64) (some 332) (cert (some 64) (some 332)).1 (cert (some 64) (some 332)).2=true := by decide +kernel
theorem case48 : branchCheck W A B C 6 (some 128) (none) (cert (some 128) (none)).1 (cert (some 128) (none)).2=true := by decide +kernel
theorem case49 : branchCheck W A B C 6 (some 128) (some 12) (cert (some 128) (some 12)).1 (cert (some 128) (some 12)).2=true := by decide +kernel
theorem case50 : branchCheck W A B C 6 (some 128) (some 68) (cert (some 128) (some 68)).1 (cert (some 128) (some 68)).2=true := by decide +kernel
theorem case51 : branchCheck W A B C 6 (some 128) (some 72) (cert (some 128) (some 72)).1 (cert (some 128) (some 72)).2=true := by decide +kernel
theorem case52 : branchCheck W A B C 6 (some 128) (some 78) (cert (some 128) (some 78)).1 (cert (some 128) (some 78)).2=true := by decide +kernel
theorem case53 : branchCheck W A B C 6 (some 128) (some 108) (cert (some 128) (some 108)).1 (cert (some 128) (some 108)).2=true := by decide +kernel
theorem case54 : branchCheck W A B C 6 (some 128) (some 204) (cert (some 128) (some 204)).1 (cert (some 128) (some 204)).2=true := by decide +kernel
theorem case55 : branchCheck W A B C 6 (some 128) (some 332) (cert (some 128) (some 332)).1 (cert (some 128) (some 332)).2=true := by decide +kernel
theorem case56 : branchCheck W A B C 6 (some 256) (none) (cert (some 256) (none)).1 (cert (some 256) (none)).2=true := by decide +kernel
theorem case57 : branchCheck W A B C 6 (some 256) (some 12) (cert (some 256) (some 12)).1 (cert (some 256) (some 12)).2=true := by decide +kernel
theorem case58 : branchCheck W A B C 6 (some 256) (some 68) (cert (some 256) (some 68)).1 (cert (some 256) (some 68)).2=true := by decide +kernel
theorem case59 : branchCheck W A B C 6 (some 256) (some 72) (cert (some 256) (some 72)).1 (cert (some 256) (some 72)).2=true := by decide +kernel
theorem case60 : branchCheck W A B C 6 (some 256) (some 78) (cert (some 256) (some 78)).1 (cert (some 256) (some 78)).2=true := by decide +kernel
theorem case61 : branchCheck W A B C 6 (some 256) (some 108) (cert (some 256) (some 108)).1 (cert (some 256) (some 108)).2=true := by decide +kernel
theorem case62 : branchCheck W A B C 6 (some 256) (some 204) (cert (some 256) (some 204)).1 (cert (some 256) (some 204)).2=true := by decide +kernel
theorem case63 : branchCheck W A B C 6 (some 256) (some 332) (cert (some 256) (some 332)).1 (cert (some 256) (some 332)).2=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    branchCheck W A B C 6 a b (cert a b).1 (cert a b).2))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, ⟨case05, ⟨case06, case07⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case08, ⟨case09, ⟨case10, ⟨case11, ⟨case12, ⟨case13, ⟨case14, case15⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case16, ⟨case17, ⟨case18, ⟨case19, ⟨case20, ⟨case21, ⟨case22, case23⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case24, ⟨case25, ⟨case26, ⟨case27, ⟨case28, ⟨case29, ⟨case30, case31⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case32, ⟨case33, ⟨case34, ⟨case35, ⟨case36, ⟨case37, ⟨case38, case39⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case40, ⟨case41, ⟨case42, ⟨case43, ⟨case44, ⟨case45, ⟨case46, case47⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case48, ⟨case49, ⟨case50, ⟨case51, ⟨case52, ⟨case53, ⟨case54, case55⟩⟩⟩⟩⟩⟩⟩, ⟨case56, ⟨case57, ⟨case58, ⟨case59, ⟨case60, ⟨case61, ⟨case62, case63⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  neighbour_in_snake (W:=W) (cs:=ds) (A:=A) (B:=B) (C:=C) (L:=6) (start:=6)
    cert canonical (by decide) (by decide) rfl supported pairA pairB checked p P r hr hP
#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.NeighbourChoice64.E195
