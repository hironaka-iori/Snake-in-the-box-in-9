import NeighbourChoice
namespace Snake9.LocalWindow.NeighbourChoice64.E157
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 114, 112]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 6, 1]
def A : List Nat := [4, 8, 16, 32, 64, 128, 256]
def B : List Nat := [80, 96, 113, 116, 120, 240, 368]
def C : List Nat := [63, 55, 51, 50, 114]
def cert : Option Nat → Option Nat → List Nat × Nat
  | none, none => ([2, 17, 18, 19, 23, 33, 34, 35, 39], 614189694980)
  | none, some 80 => ([2, 17, 18, 19, 23, 33, 34, 35, 39], 614189694980)
  | none, some 96 => ([2, 17, 18, 19, 23, 33, 34, 35, 39], 614189694980)
  | none, some 113 => ([2, 17, 18, 19, 23, 33, 34, 35, 39], 614189694980)
  | none, some 116 => ([2, 17, 18, 19, 23, 33, 34, 35, 39], 614189694980)
  | none, some 120 => ([2, 17, 18, 19, 23, 33, 34, 35, 39], 614189694980)
  | none, some 240 => ([2, 17, 18, 19, 23, 33, 34, 35, 39], 614189694980)
  | none, some 368 => ([2, 17, 18, 19, 23, 33, 34, 35, 39], 614189694980)
  | some 4, none => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 4, some 80 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 4, some 96 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 4, some 113 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 4, some 116 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 4, some 120 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 4, some 240 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 4, some 368 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 8, none => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 8, some 80 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 8, some 96 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 8, some 113 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 8, some 116 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 8, some 120 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 8, some 240 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 8, some 368 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 16, none => ([32, 33, 34, 35, 48, 49, 98], 396140812571322532457074393088)
  | some 16, some 80 => ([32, 33, 34, 35, 48, 49, 96, 98], 396140812571322532457074393088)
  | some 16, some 96 => ([2, 17, 32, 33, 34, 35, 39, 48, 49, 53, 113], 10384593717069655266913231023767556)
  | some 16, some 113 => ([32, 33, 34, 35, 48, 49, 96, 98], 396140812571322532457074393088)
  | some 16, some 116 => ([32, 33, 34, 35, 48, 49, 96, 98], 396140812571322532457074393088)
  | some 16, some 120 => ([32, 33, 34, 35, 48, 49, 96, 98], 396140812571322532457074393088)
  | some 16, some 240 => ([32, 33, 34, 35, 48, 49, 96, 98], 396140812571322532457074393088)
  | some 16, some 368 => ([32, 33, 34, 35, 48, 49, 96, 98], 396140812571322532457074393088)
  | some 32, none => ([16, 17, 18, 19, 48, 49, 82], 6044629098917570804645888)
  | some 32, some 80 => ([2, 16, 17, 18, 19, 23, 33, 48, 49, 53, 113], 10384593717069655266912625442619396)
  | some 32, some 96 => ([16, 17, 18, 19, 48, 49, 80, 82], 6044629098917570804645888)
  | some 32, some 113 => ([16, 17, 18, 19, 48, 49, 80, 82], 6044629098917570804645888)
  | some 32, some 116 => ([16, 17, 18, 19, 48, 49, 80, 82], 6044629098917570804645888)
  | some 32, some 120 => ([16, 17, 18, 19, 48, 49, 80, 82], 6044629098917570804645888)
  | some 32, some 240 => ([16, 17, 18, 19, 48, 49, 80, 82], 6044629098917570804645888)
  | some 32, some 368 => ([16, 17, 18, 19, 48, 49, 80, 82], 6044629098917570804645888)
  | some 64, none => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 64, some 80 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 64, some 96 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 64, some 113 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 64, some 116 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 64, some 120 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 64, some 240 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 64, some 368 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 128, none => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 128, some 80 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 128, some 96 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 128, some 113 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 128, some 116 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 128, some 120 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 128, some 240 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 128, some 368 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 256, none => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 256, some 80 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 256, some 96 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 256, some 113 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 256, some 116 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 256, some 120 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 256, some 240 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | some 256, some 368 => ([2, 16, 17, 18, 19, 23, 32, 33, 34, 35, 39], 614189694980)
  | _, _ => ([],0)
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem case00 : branchCheck W A B C 8 (none) (none) (cert (none) (none)).1 (cert (none) (none)).2=true := by decide +kernel
theorem case01 : branchCheck W A B C 8 (none) (some 80) (cert (none) (some 80)).1 (cert (none) (some 80)).2=true := by decide +kernel
theorem case02 : branchCheck W A B C 8 (none) (some 96) (cert (none) (some 96)).1 (cert (none) (some 96)).2=true := by decide +kernel
theorem case03 : branchCheck W A B C 8 (none) (some 113) (cert (none) (some 113)).1 (cert (none) (some 113)).2=true := by decide +kernel
theorem case04 : branchCheck W A B C 8 (none) (some 116) (cert (none) (some 116)).1 (cert (none) (some 116)).2=true := by decide +kernel
theorem case05 : branchCheck W A B C 8 (none) (some 120) (cert (none) (some 120)).1 (cert (none) (some 120)).2=true := by decide +kernel
theorem case06 : branchCheck W A B C 8 (none) (some 240) (cert (none) (some 240)).1 (cert (none) (some 240)).2=true := by decide +kernel
theorem case07 : branchCheck W A B C 8 (none) (some 368) (cert (none) (some 368)).1 (cert (none) (some 368)).2=true := by decide +kernel
theorem case08 : branchCheck W A B C 8 (some 4) (none) (cert (some 4) (none)).1 (cert (some 4) (none)).2=true := by decide +kernel
theorem case09 : branchCheck W A B C 8 (some 4) (some 80) (cert (some 4) (some 80)).1 (cert (some 4) (some 80)).2=true := by decide +kernel
theorem case10 : branchCheck W A B C 8 (some 4) (some 96) (cert (some 4) (some 96)).1 (cert (some 4) (some 96)).2=true := by decide +kernel
theorem case11 : branchCheck W A B C 8 (some 4) (some 113) (cert (some 4) (some 113)).1 (cert (some 4) (some 113)).2=true := by decide +kernel
theorem case12 : branchCheck W A B C 8 (some 4) (some 116) (cert (some 4) (some 116)).1 (cert (some 4) (some 116)).2=true := by decide +kernel
theorem case13 : branchCheck W A B C 8 (some 4) (some 120) (cert (some 4) (some 120)).1 (cert (some 4) (some 120)).2=true := by decide +kernel
theorem case14 : branchCheck W A B C 8 (some 4) (some 240) (cert (some 4) (some 240)).1 (cert (some 4) (some 240)).2=true := by decide +kernel
theorem case15 : branchCheck W A B C 8 (some 4) (some 368) (cert (some 4) (some 368)).1 (cert (some 4) (some 368)).2=true := by decide +kernel
theorem case16 : branchCheck W A B C 8 (some 8) (none) (cert (some 8) (none)).1 (cert (some 8) (none)).2=true := by decide +kernel
theorem case17 : branchCheck W A B C 8 (some 8) (some 80) (cert (some 8) (some 80)).1 (cert (some 8) (some 80)).2=true := by decide +kernel
theorem case18 : branchCheck W A B C 8 (some 8) (some 96) (cert (some 8) (some 96)).1 (cert (some 8) (some 96)).2=true := by decide +kernel
theorem case19 : branchCheck W A B C 8 (some 8) (some 113) (cert (some 8) (some 113)).1 (cert (some 8) (some 113)).2=true := by decide +kernel
theorem case20 : branchCheck W A B C 8 (some 8) (some 116) (cert (some 8) (some 116)).1 (cert (some 8) (some 116)).2=true := by decide +kernel
theorem case21 : branchCheck W A B C 8 (some 8) (some 120) (cert (some 8) (some 120)).1 (cert (some 8) (some 120)).2=true := by decide +kernel
theorem case22 : branchCheck W A B C 8 (some 8) (some 240) (cert (some 8) (some 240)).1 (cert (some 8) (some 240)).2=true := by decide +kernel
theorem case23 : branchCheck W A B C 8 (some 8) (some 368) (cert (some 8) (some 368)).1 (cert (some 8) (some 368)).2=true := by decide +kernel
theorem case24 : branchCheck W A B C 8 (some 16) (none) (cert (some 16) (none)).1 (cert (some 16) (none)).2=true := by decide +kernel
theorem case25 : branchCheck W A B C 8 (some 16) (some 80) (cert (some 16) (some 80)).1 (cert (some 16) (some 80)).2=true := by decide +kernel
theorem case26 : branchCheck W A B C 8 (some 16) (some 96) (cert (some 16) (some 96)).1 (cert (some 16) (some 96)).2=true := by decide +kernel
theorem case27 : branchCheck W A B C 8 (some 16) (some 113) (cert (some 16) (some 113)).1 (cert (some 16) (some 113)).2=true := by decide +kernel
theorem case28 : branchCheck W A B C 8 (some 16) (some 116) (cert (some 16) (some 116)).1 (cert (some 16) (some 116)).2=true := by decide +kernel
theorem case29 : branchCheck W A B C 8 (some 16) (some 120) (cert (some 16) (some 120)).1 (cert (some 16) (some 120)).2=true := by decide +kernel
theorem case30 : branchCheck W A B C 8 (some 16) (some 240) (cert (some 16) (some 240)).1 (cert (some 16) (some 240)).2=true := by decide +kernel
theorem case31 : branchCheck W A B C 8 (some 16) (some 368) (cert (some 16) (some 368)).1 (cert (some 16) (some 368)).2=true := by decide +kernel
theorem case32 : branchCheck W A B C 8 (some 32) (none) (cert (some 32) (none)).1 (cert (some 32) (none)).2=true := by decide +kernel
theorem case33 : branchCheck W A B C 8 (some 32) (some 80) (cert (some 32) (some 80)).1 (cert (some 32) (some 80)).2=true := by decide +kernel
theorem case34 : branchCheck W A B C 8 (some 32) (some 96) (cert (some 32) (some 96)).1 (cert (some 32) (some 96)).2=true := by decide +kernel
theorem case35 : branchCheck W A B C 8 (some 32) (some 113) (cert (some 32) (some 113)).1 (cert (some 32) (some 113)).2=true := by decide +kernel
theorem case36 : branchCheck W A B C 8 (some 32) (some 116) (cert (some 32) (some 116)).1 (cert (some 32) (some 116)).2=true := by decide +kernel
theorem case37 : branchCheck W A B C 8 (some 32) (some 120) (cert (some 32) (some 120)).1 (cert (some 32) (some 120)).2=true := by decide +kernel
theorem case38 : branchCheck W A B C 8 (some 32) (some 240) (cert (some 32) (some 240)).1 (cert (some 32) (some 240)).2=true := by decide +kernel
theorem case39 : branchCheck W A B C 8 (some 32) (some 368) (cert (some 32) (some 368)).1 (cert (some 32) (some 368)).2=true := by decide +kernel
theorem case40 : branchCheck W A B C 8 (some 64) (none) (cert (some 64) (none)).1 (cert (some 64) (none)).2=true := by decide +kernel
theorem case41 : branchCheck W A B C 8 (some 64) (some 80) (cert (some 64) (some 80)).1 (cert (some 64) (some 80)).2=true := by decide +kernel
theorem case42 : branchCheck W A B C 8 (some 64) (some 96) (cert (some 64) (some 96)).1 (cert (some 64) (some 96)).2=true := by decide +kernel
theorem case43 : branchCheck W A B C 8 (some 64) (some 113) (cert (some 64) (some 113)).1 (cert (some 64) (some 113)).2=true := by decide +kernel
theorem case44 : branchCheck W A B C 8 (some 64) (some 116) (cert (some 64) (some 116)).1 (cert (some 64) (some 116)).2=true := by decide +kernel
theorem case45 : branchCheck W A B C 8 (some 64) (some 120) (cert (some 64) (some 120)).1 (cert (some 64) (some 120)).2=true := by decide +kernel
theorem case46 : branchCheck W A B C 8 (some 64) (some 240) (cert (some 64) (some 240)).1 (cert (some 64) (some 240)).2=true := by decide +kernel
theorem case47 : branchCheck W A B C 8 (some 64) (some 368) (cert (some 64) (some 368)).1 (cert (some 64) (some 368)).2=true := by decide +kernel
theorem case48 : branchCheck W A B C 8 (some 128) (none) (cert (some 128) (none)).1 (cert (some 128) (none)).2=true := by decide +kernel
theorem case49 : branchCheck W A B C 8 (some 128) (some 80) (cert (some 128) (some 80)).1 (cert (some 128) (some 80)).2=true := by decide +kernel
theorem case50 : branchCheck W A B C 8 (some 128) (some 96) (cert (some 128) (some 96)).1 (cert (some 128) (some 96)).2=true := by decide +kernel
theorem case51 : branchCheck W A B C 8 (some 128) (some 113) (cert (some 128) (some 113)).1 (cert (some 128) (some 113)).2=true := by decide +kernel
theorem case52 : branchCheck W A B C 8 (some 128) (some 116) (cert (some 128) (some 116)).1 (cert (some 128) (some 116)).2=true := by decide +kernel
theorem case53 : branchCheck W A B C 8 (some 128) (some 120) (cert (some 128) (some 120)).1 (cert (some 128) (some 120)).2=true := by decide +kernel
theorem case54 : branchCheck W A B C 8 (some 128) (some 240) (cert (some 128) (some 240)).1 (cert (some 128) (some 240)).2=true := by decide +kernel
theorem case55 : branchCheck W A B C 8 (some 128) (some 368) (cert (some 128) (some 368)).1 (cert (some 128) (some 368)).2=true := by decide +kernel
theorem case56 : branchCheck W A B C 8 (some 256) (none) (cert (some 256) (none)).1 (cert (some 256) (none)).2=true := by decide +kernel
theorem case57 : branchCheck W A B C 8 (some 256) (some 80) (cert (some 256) (some 80)).1 (cert (some 256) (some 80)).2=true := by decide +kernel
theorem case58 : branchCheck W A B C 8 (some 256) (some 96) (cert (some 256) (some 96)).1 (cert (some 256) (some 96)).2=true := by decide +kernel
theorem case59 : branchCheck W A B C 8 (some 256) (some 113) (cert (some 256) (some 113)).1 (cert (some 256) (some 113)).2=true := by decide +kernel
theorem case60 : branchCheck W A B C 8 (some 256) (some 116) (cert (some 256) (some 116)).1 (cert (some 256) (some 116)).2=true := by decide +kernel
theorem case61 : branchCheck W A B C 8 (some 256) (some 120) (cert (some 256) (some 120)).1 (cert (some 256) (some 120)).2=true := by decide +kernel
theorem case62 : branchCheck W A B C 8 (some 256) (some 240) (cert (some 256) (some 240)).1 (cert (some 256) (some 240)).2=true := by decide +kernel
theorem case63 : branchCheck W A B C 8 (some 256) (some 368) (cert (some 256) (some 368)).1 (cert (some 256) (some 368)).2=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    branchCheck W A B C 8 a b (cert a b).1 (cert a b).2))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, ⟨case05, ⟨case06, case07⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case08, ⟨case09, ⟨case10, ⟨case11, ⟨case12, ⟨case13, ⟨case14, case15⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case16, ⟨case17, ⟨case18, ⟨case19, ⟨case20, ⟨case21, ⟨case22, case23⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case24, ⟨case25, ⟨case26, ⟨case27, ⟨case28, ⟨case29, ⟨case30, case31⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case32, ⟨case33, ⟨case34, ⟨case35, ⟨case36, ⟨case37, ⟨case38, case39⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case40, ⟨case41, ⟨case42, ⟨case43, ⟨case44, ⟨case45, ⟨case46, case47⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case48, ⟨case49, ⟨case50, ⟨case51, ⟨case52, ⟨case53, ⟨case54, case55⟩⟩⟩⟩⟩⟩⟩, ⟨case56, ⟨case57, ⟨case58, ⟨case59, ⟨case60, ⟨case61, ⟨case62, case63⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    8≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  neighbour_in_snake (W:=W) (cs:=ds) (A:=A) (B:=B) (C:=C) (L:=8) (start:=6)
    cert canonical (by decide) (by decide) rfl supported pairA pairB checked p P r hr hP
#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.NeighbourChoice64.E157
