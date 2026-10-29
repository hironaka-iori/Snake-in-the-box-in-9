import NeighbourChoice
namespace Snake9.LocalWindow.NeighbourChoice64.E075
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 56, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 0, 2, 1]
def A : List Nat := [4, 8, 16, 32, 64, 128, 256]
def B : List Nat := [46, 54, 126, 190, 318]
def C : List Nat := [29, 25, 57, 56, 60]
def cert : Option Nat → Option Nat → List Nat × Nat
  | none, none => ([9, 17, 33, 40, 41, 48, 49], 847736350114560)
  | none, some 46 => ([9, 17, 33, 40, 41, 48, 49], 847736350114560)
  | none, some 54 => ([9, 17, 33, 40, 41, 48, 49], 847736350114560)
  | none, some 126 => ([9, 17, 33, 40, 41, 48, 49], 847736350114560)
  | none, some 190 => ([9, 17, 33, 40, 41, 48, 49], 847736350114560)
  | none, some 318 => ([9, 17, 33, 40, 41, 48, 49], 847736350114560)
  | some 4, none => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 4, some 46 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 4, some 54 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 4, some 126 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 4, some 190 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 4, some 318 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 8, none => ([5, 16, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361123872)
  | some 8, some 46 => ([5, 16, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361123872)
  | some 8, some 54 => ([5, 16, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361123872)
  | some 8, some 126 => ([5, 16, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361123872)
  | some 8, some 190 => ([5, 16, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361123872)
  | some 8, some 318 => ([5, 16, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361123872)
  | some 16, none => ([5, 8, 9, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361059104)
  | some 16, some 46 => ([5, 8, 9, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361059104)
  | some 16, some 54 => ([5, 8, 9, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361059104)
  | some 16, some 126 => ([5, 8, 9, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361059104)
  | some 16, some 190 => ([5, 8, 9, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361059104)
  | some 16, some 318 => ([5, 8, 9, 17, 19, 21, 23, 32, 33, 40, 41, 48, 49], 847736361059104)
  | some 32, none => ([5, 8, 9, 11, 16, 17, 19, 21, 23, 33, 40, 41, 44, 48, 49, 52], 5368923879574304)
  | some 32, some 46 => ([5, 8, 9, 11, 16, 17, 19, 21, 23, 33, 40, 41, 44, 48, 49, 52], 5368923879574304)
  | some 32, some 54 => ([5, 8, 9, 11, 16, 17, 19, 21, 23, 33, 40, 41, 44, 48, 49, 52], 5368923879574304)
  | some 32, some 126 => ([5, 8, 9, 11, 16, 17, 19, 21, 23, 33, 40, 41, 44, 48, 49, 52], 5368923879574304)
  | some 32, some 190 => ([5, 8, 9, 11, 16, 17, 19, 21, 23, 33, 40, 41, 44, 48, 49, 52], 5368923879574304)
  | some 32, some 318 => ([5, 8, 9, 11, 16, 17, 19, 21, 23, 33, 40, 41, 44, 48, 49, 52], 5368923879574304)
  | some 64, none => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 64, some 46 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 64, some 54 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 64, some 126 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 64, some 190 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 64, some 318 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 128, none => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 128, some 46 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 128, some 54 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 128, some 126 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 128, some 190 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 128, some 318 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 256, none => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 256, some 46 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 256, some 54 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 256, some 126 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 256, some 190 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | some 256, some 318 => ([8, 9, 16, 17, 32, 33, 40, 41, 48, 49], 847736350114560)
  | _, _ => ([],0)
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem case00 : branchCheck W A B C 16 (none) (none) (cert (none) (none)).1 (cert (none) (none)).2=true := by decide +kernel
theorem case01 : branchCheck W A B C 16 (none) (some 46) (cert (none) (some 46)).1 (cert (none) (some 46)).2=true := by decide +kernel
theorem case02 : branchCheck W A B C 16 (none) (some 54) (cert (none) (some 54)).1 (cert (none) (some 54)).2=true := by decide +kernel
theorem case03 : branchCheck W A B C 16 (none) (some 126) (cert (none) (some 126)).1 (cert (none) (some 126)).2=true := by decide +kernel
theorem case04 : branchCheck W A B C 16 (none) (some 190) (cert (none) (some 190)).1 (cert (none) (some 190)).2=true := by decide +kernel
theorem case05 : branchCheck W A B C 16 (none) (some 318) (cert (none) (some 318)).1 (cert (none) (some 318)).2=true := by decide +kernel
theorem case06 : branchCheck W A B C 16 (some 4) (none) (cert (some 4) (none)).1 (cert (some 4) (none)).2=true := by decide +kernel
theorem case07 : branchCheck W A B C 16 (some 4) (some 46) (cert (some 4) (some 46)).1 (cert (some 4) (some 46)).2=true := by decide +kernel
theorem case08 : branchCheck W A B C 16 (some 4) (some 54) (cert (some 4) (some 54)).1 (cert (some 4) (some 54)).2=true := by decide +kernel
theorem case09 : branchCheck W A B C 16 (some 4) (some 126) (cert (some 4) (some 126)).1 (cert (some 4) (some 126)).2=true := by decide +kernel
theorem case10 : branchCheck W A B C 16 (some 4) (some 190) (cert (some 4) (some 190)).1 (cert (some 4) (some 190)).2=true := by decide +kernel
theorem case11 : branchCheck W A B C 16 (some 4) (some 318) (cert (some 4) (some 318)).1 (cert (some 4) (some 318)).2=true := by decide +kernel
theorem case12 : branchCheck W A B C 16 (some 8) (none) (cert (some 8) (none)).1 (cert (some 8) (none)).2=true := by decide +kernel
theorem case13 : branchCheck W A B C 16 (some 8) (some 46) (cert (some 8) (some 46)).1 (cert (some 8) (some 46)).2=true := by decide +kernel
theorem case14 : branchCheck W A B C 16 (some 8) (some 54) (cert (some 8) (some 54)).1 (cert (some 8) (some 54)).2=true := by decide +kernel
theorem case15 : branchCheck W A B C 16 (some 8) (some 126) (cert (some 8) (some 126)).1 (cert (some 8) (some 126)).2=true := by decide +kernel
theorem case16 : branchCheck W A B C 16 (some 8) (some 190) (cert (some 8) (some 190)).1 (cert (some 8) (some 190)).2=true := by decide +kernel
theorem case17 : branchCheck W A B C 16 (some 8) (some 318) (cert (some 8) (some 318)).1 (cert (some 8) (some 318)).2=true := by decide +kernel
theorem case18 : branchCheck W A B C 16 (some 16) (none) (cert (some 16) (none)).1 (cert (some 16) (none)).2=true := by decide +kernel
theorem case19 : branchCheck W A B C 16 (some 16) (some 46) (cert (some 16) (some 46)).1 (cert (some 16) (some 46)).2=true := by decide +kernel
theorem case20 : branchCheck W A B C 16 (some 16) (some 54) (cert (some 16) (some 54)).1 (cert (some 16) (some 54)).2=true := by decide +kernel
theorem case21 : branchCheck W A B C 16 (some 16) (some 126) (cert (some 16) (some 126)).1 (cert (some 16) (some 126)).2=true := by decide +kernel
theorem case22 : branchCheck W A B C 16 (some 16) (some 190) (cert (some 16) (some 190)).1 (cert (some 16) (some 190)).2=true := by decide +kernel
theorem case23 : branchCheck W A B C 16 (some 16) (some 318) (cert (some 16) (some 318)).1 (cert (some 16) (some 318)).2=true := by decide +kernel
theorem case24 : branchCheck W A B C 16 (some 32) (none) (cert (some 32) (none)).1 (cert (some 32) (none)).2=true := by decide +kernel
theorem case25 : branchCheck W A B C 16 (some 32) (some 46) (cert (some 32) (some 46)).1 (cert (some 32) (some 46)).2=true := by decide +kernel
theorem case26 : branchCheck W A B C 16 (some 32) (some 54) (cert (some 32) (some 54)).1 (cert (some 32) (some 54)).2=true := by decide +kernel
theorem case27 : branchCheck W A B C 16 (some 32) (some 126) (cert (some 32) (some 126)).1 (cert (some 32) (some 126)).2=true := by decide +kernel
theorem case28 : branchCheck W A B C 16 (some 32) (some 190) (cert (some 32) (some 190)).1 (cert (some 32) (some 190)).2=true := by decide +kernel
theorem case29 : branchCheck W A B C 16 (some 32) (some 318) (cert (some 32) (some 318)).1 (cert (some 32) (some 318)).2=true := by decide +kernel
theorem case30 : branchCheck W A B C 16 (some 64) (none) (cert (some 64) (none)).1 (cert (some 64) (none)).2=true := by decide +kernel
theorem case31 : branchCheck W A B C 16 (some 64) (some 46) (cert (some 64) (some 46)).1 (cert (some 64) (some 46)).2=true := by decide +kernel
theorem case32 : branchCheck W A B C 16 (some 64) (some 54) (cert (some 64) (some 54)).1 (cert (some 64) (some 54)).2=true := by decide +kernel
theorem case33 : branchCheck W A B C 16 (some 64) (some 126) (cert (some 64) (some 126)).1 (cert (some 64) (some 126)).2=true := by decide +kernel
theorem case34 : branchCheck W A B C 16 (some 64) (some 190) (cert (some 64) (some 190)).1 (cert (some 64) (some 190)).2=true := by decide +kernel
theorem case35 : branchCheck W A B C 16 (some 64) (some 318) (cert (some 64) (some 318)).1 (cert (some 64) (some 318)).2=true := by decide +kernel
theorem case36 : branchCheck W A B C 16 (some 128) (none) (cert (some 128) (none)).1 (cert (some 128) (none)).2=true := by decide +kernel
theorem case37 : branchCheck W A B C 16 (some 128) (some 46) (cert (some 128) (some 46)).1 (cert (some 128) (some 46)).2=true := by decide +kernel
theorem case38 : branchCheck W A B C 16 (some 128) (some 54) (cert (some 128) (some 54)).1 (cert (some 128) (some 54)).2=true := by decide +kernel
theorem case39 : branchCheck W A B C 16 (some 128) (some 126) (cert (some 128) (some 126)).1 (cert (some 128) (some 126)).2=true := by decide +kernel
theorem case40 : branchCheck W A B C 16 (some 128) (some 190) (cert (some 128) (some 190)).1 (cert (some 128) (some 190)).2=true := by decide +kernel
theorem case41 : branchCheck W A B C 16 (some 128) (some 318) (cert (some 128) (some 318)).1 (cert (some 128) (some 318)).2=true := by decide +kernel
theorem case42 : branchCheck W A B C 16 (some 256) (none) (cert (some 256) (none)).1 (cert (some 256) (none)).2=true := by decide +kernel
theorem case43 : branchCheck W A B C 16 (some 256) (some 46) (cert (some 256) (some 46)).1 (cert (some 256) (some 46)).2=true := by decide +kernel
theorem case44 : branchCheck W A B C 16 (some 256) (some 54) (cert (some 256) (some 54)).1 (cert (some 256) (some 54)).2=true := by decide +kernel
theorem case45 : branchCheck W A B C 16 (some 256) (some 126) (cert (some 256) (some 126)).1 (cert (some 256) (some 126)).2=true := by decide +kernel
theorem case46 : branchCheck W A B C 16 (some 256) (some 190) (cert (some 256) (some 190)).1 (cert (some 256) (some 190)).2=true := by decide +kernel
theorem case47 : branchCheck W A B C 16 (some 256) (some 318) (cert (some 256) (some 318)).1 (cert (some 256) (some 318)).2=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    branchCheck W A B C 16 a b (cert a b).1 (cert a b).2))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, case05⟩⟩⟩⟩⟩, ⟨⟨case06, ⟨case07, ⟨case08, ⟨case09, ⟨case10, case11⟩⟩⟩⟩⟩, ⟨⟨case12, ⟨case13, ⟨case14, ⟨case15, ⟨case16, case17⟩⟩⟩⟩⟩, ⟨⟨case18, ⟨case19, ⟨case20, ⟨case21, ⟨case22, case23⟩⟩⟩⟩⟩, ⟨⟨case24, ⟨case25, ⟨case26, ⟨case27, ⟨case28, case29⟩⟩⟩⟩⟩, ⟨⟨case30, ⟨case31, ⟨case32, ⟨case33, ⟨case34, case35⟩⟩⟩⟩⟩, ⟨⟨case36, ⟨case37, ⟨case38, ⟨case39, ⟨case40, case41⟩⟩⟩⟩⟩, ⟨case42, ⟨case43, ⟨case44, ⟨case45, ⟨case46, case47⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    16≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  neighbour_in_snake (W:=W) (cs:=ds) (A:=A) (B:=B) (C:=C) (L:=16) (start:=6)
    cert canonical (by decide) (by decide) rfl supported pairA pairB checked p P r hr hP
#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.NeighbourChoice64.E075
