import NeighbourChoice
namespace Snake9.LocalWindow.NeighbourChoice64.E095
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 120, 104]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 6, 4]
def A : List Nat := [4, 8, 16, 32, 64, 128, 256]
def B : List Nat := [72, 96, 105, 106, 108, 232, 360]
def C : List Nat := [27, 25, 57, 56, 120]
def cert : Option Nat → Option Nat → List Nat × Nat
  | none, none => ([9, 33, 40, 41, 48, 49], 847736349917952)
  | none, some 72 => ([9, 33, 40, 41, 48, 49], 847736349917952)
  | none, some 96 => ([9, 33, 40, 41, 48, 49], 847736349917952)
  | none, some 105 => ([9, 33, 40, 41, 48, 49], 847736349917952)
  | none, some 106 => ([9, 33, 40, 41, 48, 49], 847736349917952)
  | none, some 108 => ([9, 33, 40, 41, 48, 49], 847736349917952)
  | none, some 232 => ([9, 33, 40, 41, 48, 49], 847736349917952)
  | none, some 360 => ([9, 33, 40, 41, 48, 49], 847736349917952)
  | some 4, none => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 4, some 72 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 4, some 96 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 4, some 105 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 4, some 106 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 4, some 108 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 4, some 232 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 4, some 360 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 8, none => ([16, 17, 32, 33, 40, 41, 48, 49], 847736350113792)
  | some 8, some 72 => ([10, 14, 16, 17, 19, 26, 30, 32, 33, 48, 49], 844438956622848)
  | some 8, some 96 => ([16, 17, 32, 33, 40, 41, 48, 49], 847736350113792)
  | some 8, some 105 => ([16, 17, 32, 33, 40, 41, 48, 49], 847736350113792)
  | some 8, some 106 => ([16, 17, 32, 33, 40, 41, 48, 49], 847736350113792)
  | some 8, some 108 => ([16, 17, 32, 33, 40, 41, 48, 49], 847736350113792)
  | some 8, some 232 => ([16, 17, 32, 33, 40, 41, 48, 49], 847736350113792)
  | some 8, some 360 => ([16, 17, 32, 33, 40, 41, 48, 49], 847736350113792)
  | some 16, none => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 16, some 72 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 16, some 96 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 16, some 105 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 16, some 106 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 16, some 108 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 16, some 232 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 16, some 360 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 32, none => ([8, 9, 16, 17, 24, 40, 41, 48, 49, 88], 309489732188675661851984640)
  | some 32, some 72 => ([8, 9, 11, 16, 17, 19, 33, 40, 41, 48, 49, 112], 5192296858534827629378228384893696)
  | some 32, some 96 => ([8, 9, 16, 17, 24, 40, 41, 48, 49, 72, 88], 309489732188675661851984640)
  | some 32, some 105 => ([8, 9, 16, 17, 24, 40, 41, 48, 49, 72, 88], 309489732188675661851984640)
  | some 32, some 106 => ([8, 9, 16, 17, 24, 40, 41, 48, 49, 72, 88], 309489732188675661851984640)
  | some 32, some 108 => ([8, 9, 16, 17, 24, 40, 41, 48, 49, 72, 88], 309489732188675661851984640)
  | some 32, some 232 => ([8, 9, 16, 17, 24, 40, 41, 48, 49, 72, 88], 309489732188675661851984640)
  | some 32, some 360 => ([8, 9, 16, 17, 24, 40, 41, 48, 49, 72, 88], 309489732188675661851984640)
  | some 64, none => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 64, some 72 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 64, some 96 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 64, some 105 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 64, some 106 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 64, some 108 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 64, some 232 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 64, some 360 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 128, none => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 128, some 72 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 128, some 96 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 128, some 105 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 128, some 106 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 128, some 108 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 128, some 232 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 128, some 360 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 256, none => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 256, some 72 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 256, some 96 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 256, some 105 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 256, some 106 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 256, some 108 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 256, some 232 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | some 256, some 360 => ([8, 9, 32, 33, 40, 41, 48, 49], 847736349917952)
  | _, _ => ([],0)
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem case00 : branchCheck W A B C 11 (none) (none) (cert (none) (none)).1 (cert (none) (none)).2=true := by decide +kernel
theorem case01 : branchCheck W A B C 11 (none) (some 72) (cert (none) (some 72)).1 (cert (none) (some 72)).2=true := by decide +kernel
theorem case02 : branchCheck W A B C 11 (none) (some 96) (cert (none) (some 96)).1 (cert (none) (some 96)).2=true := by decide +kernel
theorem case03 : branchCheck W A B C 11 (none) (some 105) (cert (none) (some 105)).1 (cert (none) (some 105)).2=true := by decide +kernel
theorem case04 : branchCheck W A B C 11 (none) (some 106) (cert (none) (some 106)).1 (cert (none) (some 106)).2=true := by decide +kernel
theorem case05 : branchCheck W A B C 11 (none) (some 108) (cert (none) (some 108)).1 (cert (none) (some 108)).2=true := by decide +kernel
theorem case06 : branchCheck W A B C 11 (none) (some 232) (cert (none) (some 232)).1 (cert (none) (some 232)).2=true := by decide +kernel
theorem case07 : branchCheck W A B C 11 (none) (some 360) (cert (none) (some 360)).1 (cert (none) (some 360)).2=true := by decide +kernel
theorem case08 : branchCheck W A B C 11 (some 4) (none) (cert (some 4) (none)).1 (cert (some 4) (none)).2=true := by decide +kernel
theorem case09 : branchCheck W A B C 11 (some 4) (some 72) (cert (some 4) (some 72)).1 (cert (some 4) (some 72)).2=true := by decide +kernel
theorem case10 : branchCheck W A B C 11 (some 4) (some 96) (cert (some 4) (some 96)).1 (cert (some 4) (some 96)).2=true := by decide +kernel
theorem case11 : branchCheck W A B C 11 (some 4) (some 105) (cert (some 4) (some 105)).1 (cert (some 4) (some 105)).2=true := by decide +kernel
theorem case12 : branchCheck W A B C 11 (some 4) (some 106) (cert (some 4) (some 106)).1 (cert (some 4) (some 106)).2=true := by decide +kernel
theorem case13 : branchCheck W A B C 11 (some 4) (some 108) (cert (some 4) (some 108)).1 (cert (some 4) (some 108)).2=true := by decide +kernel
theorem case14 : branchCheck W A B C 11 (some 4) (some 232) (cert (some 4) (some 232)).1 (cert (some 4) (some 232)).2=true := by decide +kernel
theorem case15 : branchCheck W A B C 11 (some 4) (some 360) (cert (some 4) (some 360)).1 (cert (some 4) (some 360)).2=true := by decide +kernel
theorem case16 : branchCheck W A B C 11 (some 8) (none) (cert (some 8) (none)).1 (cert (some 8) (none)).2=true := by decide +kernel
theorem case17 : branchCheck W A B C 11 (some 8) (some 72) (cert (some 8) (some 72)).1 (cert (some 8) (some 72)).2=true := by decide +kernel
theorem case18 : branchCheck W A B C 11 (some 8) (some 96) (cert (some 8) (some 96)).1 (cert (some 8) (some 96)).2=true := by decide +kernel
theorem case19 : branchCheck W A B C 11 (some 8) (some 105) (cert (some 8) (some 105)).1 (cert (some 8) (some 105)).2=true := by decide +kernel
theorem case20 : branchCheck W A B C 11 (some 8) (some 106) (cert (some 8) (some 106)).1 (cert (some 8) (some 106)).2=true := by decide +kernel
theorem case21 : branchCheck W A B C 11 (some 8) (some 108) (cert (some 8) (some 108)).1 (cert (some 8) (some 108)).2=true := by decide +kernel
theorem case22 : branchCheck W A B C 11 (some 8) (some 232) (cert (some 8) (some 232)).1 (cert (some 8) (some 232)).2=true := by decide +kernel
theorem case23 : branchCheck W A B C 11 (some 8) (some 360) (cert (some 8) (some 360)).1 (cert (some 8) (some 360)).2=true := by decide +kernel
theorem case24 : branchCheck W A B C 11 (some 16) (none) (cert (some 16) (none)).1 (cert (some 16) (none)).2=true := by decide +kernel
theorem case25 : branchCheck W A B C 11 (some 16) (some 72) (cert (some 16) (some 72)).1 (cert (some 16) (some 72)).2=true := by decide +kernel
theorem case26 : branchCheck W A B C 11 (some 16) (some 96) (cert (some 16) (some 96)).1 (cert (some 16) (some 96)).2=true := by decide +kernel
theorem case27 : branchCheck W A B C 11 (some 16) (some 105) (cert (some 16) (some 105)).1 (cert (some 16) (some 105)).2=true := by decide +kernel
theorem case28 : branchCheck W A B C 11 (some 16) (some 106) (cert (some 16) (some 106)).1 (cert (some 16) (some 106)).2=true := by decide +kernel
theorem case29 : branchCheck W A B C 11 (some 16) (some 108) (cert (some 16) (some 108)).1 (cert (some 16) (some 108)).2=true := by decide +kernel
theorem case30 : branchCheck W A B C 11 (some 16) (some 232) (cert (some 16) (some 232)).1 (cert (some 16) (some 232)).2=true := by decide +kernel
theorem case31 : branchCheck W A B C 11 (some 16) (some 360) (cert (some 16) (some 360)).1 (cert (some 16) (some 360)).2=true := by decide +kernel
theorem case32 : branchCheck W A B C 11 (some 32) (none) (cert (some 32) (none)).1 (cert (some 32) (none)).2=true := by decide +kernel
theorem case33 : branchCheck W A B C 11 (some 32) (some 72) (cert (some 32) (some 72)).1 (cert (some 32) (some 72)).2=true := by decide +kernel
theorem case34 : branchCheck W A B C 11 (some 32) (some 96) (cert (some 32) (some 96)).1 (cert (some 32) (some 96)).2=true := by decide +kernel
theorem case35 : branchCheck W A B C 11 (some 32) (some 105) (cert (some 32) (some 105)).1 (cert (some 32) (some 105)).2=true := by decide +kernel
theorem case36 : branchCheck W A B C 11 (some 32) (some 106) (cert (some 32) (some 106)).1 (cert (some 32) (some 106)).2=true := by decide +kernel
theorem case37 : branchCheck W A B C 11 (some 32) (some 108) (cert (some 32) (some 108)).1 (cert (some 32) (some 108)).2=true := by decide +kernel
theorem case38 : branchCheck W A B C 11 (some 32) (some 232) (cert (some 32) (some 232)).1 (cert (some 32) (some 232)).2=true := by decide +kernel
theorem case39 : branchCheck W A B C 11 (some 32) (some 360) (cert (some 32) (some 360)).1 (cert (some 32) (some 360)).2=true := by decide +kernel
theorem case40 : branchCheck W A B C 11 (some 64) (none) (cert (some 64) (none)).1 (cert (some 64) (none)).2=true := by decide +kernel
theorem case41 : branchCheck W A B C 11 (some 64) (some 72) (cert (some 64) (some 72)).1 (cert (some 64) (some 72)).2=true := by decide +kernel
theorem case42 : branchCheck W A B C 11 (some 64) (some 96) (cert (some 64) (some 96)).1 (cert (some 64) (some 96)).2=true := by decide +kernel
theorem case43 : branchCheck W A B C 11 (some 64) (some 105) (cert (some 64) (some 105)).1 (cert (some 64) (some 105)).2=true := by decide +kernel
theorem case44 : branchCheck W A B C 11 (some 64) (some 106) (cert (some 64) (some 106)).1 (cert (some 64) (some 106)).2=true := by decide +kernel
theorem case45 : branchCheck W A B C 11 (some 64) (some 108) (cert (some 64) (some 108)).1 (cert (some 64) (some 108)).2=true := by decide +kernel
theorem case46 : branchCheck W A B C 11 (some 64) (some 232) (cert (some 64) (some 232)).1 (cert (some 64) (some 232)).2=true := by decide +kernel
theorem case47 : branchCheck W A B C 11 (some 64) (some 360) (cert (some 64) (some 360)).1 (cert (some 64) (some 360)).2=true := by decide +kernel
theorem case48 : branchCheck W A B C 11 (some 128) (none) (cert (some 128) (none)).1 (cert (some 128) (none)).2=true := by decide +kernel
theorem case49 : branchCheck W A B C 11 (some 128) (some 72) (cert (some 128) (some 72)).1 (cert (some 128) (some 72)).2=true := by decide +kernel
theorem case50 : branchCheck W A B C 11 (some 128) (some 96) (cert (some 128) (some 96)).1 (cert (some 128) (some 96)).2=true := by decide +kernel
theorem case51 : branchCheck W A B C 11 (some 128) (some 105) (cert (some 128) (some 105)).1 (cert (some 128) (some 105)).2=true := by decide +kernel
theorem case52 : branchCheck W A B C 11 (some 128) (some 106) (cert (some 128) (some 106)).1 (cert (some 128) (some 106)).2=true := by decide +kernel
theorem case53 : branchCheck W A B C 11 (some 128) (some 108) (cert (some 128) (some 108)).1 (cert (some 128) (some 108)).2=true := by decide +kernel
theorem case54 : branchCheck W A B C 11 (some 128) (some 232) (cert (some 128) (some 232)).1 (cert (some 128) (some 232)).2=true := by decide +kernel
theorem case55 : branchCheck W A B C 11 (some 128) (some 360) (cert (some 128) (some 360)).1 (cert (some 128) (some 360)).2=true := by decide +kernel
theorem case56 : branchCheck W A B C 11 (some 256) (none) (cert (some 256) (none)).1 (cert (some 256) (none)).2=true := by decide +kernel
theorem case57 : branchCheck W A B C 11 (some 256) (some 72) (cert (some 256) (some 72)).1 (cert (some 256) (some 72)).2=true := by decide +kernel
theorem case58 : branchCheck W A B C 11 (some 256) (some 96) (cert (some 256) (some 96)).1 (cert (some 256) (some 96)).2=true := by decide +kernel
theorem case59 : branchCheck W A B C 11 (some 256) (some 105) (cert (some 256) (some 105)).1 (cert (some 256) (some 105)).2=true := by decide +kernel
theorem case60 : branchCheck W A B C 11 (some 256) (some 106) (cert (some 256) (some 106)).1 (cert (some 256) (some 106)).2=true := by decide +kernel
theorem case61 : branchCheck W A B C 11 (some 256) (some 108) (cert (some 256) (some 108)).1 (cert (some 256) (some 108)).2=true := by decide +kernel
theorem case62 : branchCheck W A B C 11 (some 256) (some 232) (cert (some 256) (some 232)).1 (cert (some 256) (some 232)).2=true := by decide +kernel
theorem case63 : branchCheck W A B C 11 (some 256) (some 360) (cert (some 256) (some 360)).1 (cert (some 256) (some 360)).2=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    branchCheck W A B C 11 a b (cert a b).1 (cert a b).2))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, ⟨case05, ⟨case06, case07⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case08, ⟨case09, ⟨case10, ⟨case11, ⟨case12, ⟨case13, ⟨case14, case15⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case16, ⟨case17, ⟨case18, ⟨case19, ⟨case20, ⟨case21, ⟨case22, case23⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case24, ⟨case25, ⟨case26, ⟨case27, ⟨case28, ⟨case29, ⟨case30, case31⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case32, ⟨case33, ⟨case34, ⟨case35, ⟨case36, ⟨case37, ⟨case38, case39⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case40, ⟨case41, ⟨case42, ⟨case43, ⟨case44, ⟨case45, ⟨case46, case47⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case48, ⟨case49, ⟨case50, ⟨case51, ⟨case52, ⟨case53, ⟨case54, case55⟩⟩⟩⟩⟩⟩⟩, ⟨case56, ⟨case57, ⟨case58, ⟨case59, ⟨case60, ⟨case61, ⟨case62, case63⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    11≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  neighbour_in_snake (W:=W) (cs:=ds) (A:=A) (B:=B) (C:=C) (L:=11) (start:=6)
    cert canonical (by decide) (by decide) rfl supported pairA pairB checked p P r hr hP
#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.NeighbourChoice64.E095
