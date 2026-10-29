import NeighbourChoice
namespace Snake9.LocalWindow.NeighbourChoice64.E101
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 61, 45, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 0]
def A : List Nat := [4, 8, 16, 32, 64, 128, 256]
def B : List Nat := [12, 36, 40, 46, 108, 172, 300]
def C : List Nat := [27, 25, 57, 61, 45]
def cert : Option Nat → Option Nat → List Nat × Nat
  | none, none => ([5, 9, 11, 13, 33, 35, 37, 39], 803158899504)
  | none, some 12 => ([5, 9, 33, 36, 37, 40, 41], 3517578216240)
  | none, some 36 => ([9, 12, 13, 33, 40, 41], 3311419798272)
  | none, some 40 => ([5, 9, 11, 12, 13, 33, 35, 36, 37, 39], 803158899504)
  | none, some 46 => ([5, 9, 11, 12, 13, 33, 35, 36, 37, 39], 803158899504)
  | none, some 108 => ([5, 9, 11, 12, 13, 33, 35, 36, 37, 39], 803158899504)
  | none, some 172 => ([5, 9, 11, 12, 13, 33, 35, 36, 37, 39], 803158899504)
  | none, some 300 => ([5, 9, 11, 12, 13, 33, 35, 36, 37, 39], 803158899504)
  | some 4, none => ([8, 9, 13, 32, 33, 41], 3311419798272)
  | some 4, some 12 => ([8, 9, 11, 24, 26, 28, 30, 32, 33, 40, 41], 3312845851392)
  | some 4, some 36 => ([8, 9, 12, 13, 32, 33, 40, 41], 3311419798272)
  | some 4, some 40 => ([5, 8, 9, 11, 12, 13, 17, 32, 33, 36, 37, 39, 49, 53], 9570918007454496)
  | some 4, some 46 => ([8, 9, 12, 13, 32, 33, 40, 41], 3311419798272)
  | some 4, some 108 => ([8, 9, 12, 13, 32, 33, 40, 41], 3311419798272)
  | some 4, some 172 => ([8, 9, 12, 13, 32, 33, 40, 41], 3311419798272)
  | some 4, some 300 => ([8, 9, 12, 13, 32, 33, 40, 41], 3311419798272)
  | some 8, none => ([4, 5, 9, 13, 32, 33, 35, 37, 39, 41], 4101693780528)
  | some 8, some 12 => ([4, 5, 10, 14, 16, 24, 26, 28, 30, 32, 33, 35, 36, 37, 39], 804585030704)
  | some 8, some 36 => ([4, 5, 9, 12, 13, 17, 32, 33, 35, 37, 39, 40, 41, 49, 53], 9574182182597168)
  | some 8, some 40 => ([4, 5, 9, 10, 12, 13, 14, 24, 26, 30, 32, 33, 35, 36, 37, 39, 53], 9008003571283504)
  | some 8, some 46 => ([4, 5, 9, 12, 13, 32, 33, 35, 36, 37, 39, 40, 41], 4101693780528)
  | some 8, some 108 => ([4, 5, 9, 12, 13, 32, 33, 35, 36, 37, 39, 40, 41], 4101693780528)
  | some 8, some 172 => ([4, 5, 9, 12, 13, 32, 33, 35, 36, 37, 39, 40, 41], 4101693780528)
  | some 8, some 300 => ([4, 5, 9, 12, 13, 32, 33, 35, 36, 37, 39, 40, 41], 4101693780528)
  | some 16, none => ([4, 5, 8, 9, 11, 13, 32, 33, 35, 37, 39], 803158899504)
  | some 16, some 12 => ([4, 5, 8, 9, 32, 33, 36, 37, 40, 41], 3517578216240)
  | some 16, some 36 => ([8, 9, 12, 13, 32, 33, 40, 41], 3311419798272)
  | some 16, some 40 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 16, some 46 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 16, some 108 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 16, some 172 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 16, some 300 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 32, none => ([4, 5, 8, 9, 13, 33, 37, 41], 3513283261232)
  | some 32, some 12 => ([4, 5, 8, 9, 11, 17, 33, 36, 37, 40, 41, 49, 53], 9573662491544368)
  | some 32, some 36 => ([4, 5, 8, 9, 12, 13, 33, 35, 37, 39, 40, 41], 4028679336752)
  | some 32, some 40 => ([4, 5, 8, 9, 11, 12, 13, 16, 17, 33, 35, 36, 37, 39, 48, 49], 845223794260784)
  | some 32, some 46 => ([4, 5, 8, 9, 12, 13, 33, 36, 37, 40, 41], 3513283261232)
  | some 32, some 108 => ([4, 5, 8, 9, 12, 13, 33, 36, 37, 40, 41], 3513283261232)
  | some 32, some 172 => ([4, 5, 8, 9, 12, 13, 33, 36, 37, 40, 41], 3513283261232)
  | some 32, some 300 => ([4, 5, 8, 9, 12, 13, 33, 36, 37, 40, 41], 3513283261232)
  | some 64, none => ([4, 5, 8, 9, 11, 13, 32, 33, 35, 37, 39], 803158899504)
  | some 64, some 12 => ([4, 5, 8, 9, 32, 33, 36, 37, 40, 41], 3517578216240)
  | some 64, some 36 => ([8, 9, 12, 13, 32, 33, 40, 41], 3311419798272)
  | some 64, some 40 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 64, some 46 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 64, some 108 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 64, some 172 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 64, some 300 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 128, none => ([4, 5, 8, 9, 11, 13, 32, 33, 35, 37, 39], 803158899504)
  | some 128, some 12 => ([4, 5, 8, 9, 32, 33, 36, 37, 40, 41], 3517578216240)
  | some 128, some 36 => ([8, 9, 12, 13, 32, 33, 40, 41], 3311419798272)
  | some 128, some 40 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 128, some 46 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 128, some 108 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 128, some 172 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 128, some 300 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 256, none => ([4, 5, 8, 9, 11, 13, 32, 33, 35, 37, 39], 803158899504)
  | some 256, some 12 => ([4, 5, 8, 9, 32, 33, 36, 37, 40, 41], 3517578216240)
  | some 256, some 36 => ([8, 9, 12, 13, 32, 33, 40, 41], 3311419798272)
  | some 256, some 40 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 256, some 46 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 256, some 108 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 256, some 172 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | some 256, some 300 => ([4, 5, 8, 9, 11, 12, 13, 32, 33, 35, 36, 37, 39], 803158899504)
  | _, _ => ([],0)
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem case00 : branchCheck W A B C 13 (none) (none) (cert (none) (none)).1 (cert (none) (none)).2=true := by decide +kernel
theorem case01 : branchCheck W A B C 13 (none) (some 12) (cert (none) (some 12)).1 (cert (none) (some 12)).2=true := by decide +kernel
theorem case02 : branchCheck W A B C 13 (none) (some 36) (cert (none) (some 36)).1 (cert (none) (some 36)).2=true := by decide +kernel
theorem case03 : branchCheck W A B C 13 (none) (some 40) (cert (none) (some 40)).1 (cert (none) (some 40)).2=true := by decide +kernel
theorem case04 : branchCheck W A B C 13 (none) (some 46) (cert (none) (some 46)).1 (cert (none) (some 46)).2=true := by decide +kernel
theorem case05 : branchCheck W A B C 13 (none) (some 108) (cert (none) (some 108)).1 (cert (none) (some 108)).2=true := by decide +kernel
theorem case06 : branchCheck W A B C 13 (none) (some 172) (cert (none) (some 172)).1 (cert (none) (some 172)).2=true := by decide +kernel
theorem case07 : branchCheck W A B C 13 (none) (some 300) (cert (none) (some 300)).1 (cert (none) (some 300)).2=true := by decide +kernel
theorem case08 : branchCheck W A B C 13 (some 4) (none) (cert (some 4) (none)).1 (cert (some 4) (none)).2=true := by decide +kernel
theorem case09 : branchCheck W A B C 13 (some 4) (some 12) (cert (some 4) (some 12)).1 (cert (some 4) (some 12)).2=true := by decide +kernel
theorem case10 : branchCheck W A B C 13 (some 4) (some 36) (cert (some 4) (some 36)).1 (cert (some 4) (some 36)).2=true := by decide +kernel
theorem case11 : branchCheck W A B C 13 (some 4) (some 40) (cert (some 4) (some 40)).1 (cert (some 4) (some 40)).2=true := by decide +kernel
theorem case12 : branchCheck W A B C 13 (some 4) (some 46) (cert (some 4) (some 46)).1 (cert (some 4) (some 46)).2=true := by decide +kernel
theorem case13 : branchCheck W A B C 13 (some 4) (some 108) (cert (some 4) (some 108)).1 (cert (some 4) (some 108)).2=true := by decide +kernel
theorem case14 : branchCheck W A B C 13 (some 4) (some 172) (cert (some 4) (some 172)).1 (cert (some 4) (some 172)).2=true := by decide +kernel
theorem case15 : branchCheck W A B C 13 (some 4) (some 300) (cert (some 4) (some 300)).1 (cert (some 4) (some 300)).2=true := by decide +kernel
theorem case16 : branchCheck W A B C 13 (some 8) (none) (cert (some 8) (none)).1 (cert (some 8) (none)).2=true := by decide +kernel
theorem case17 : branchCheck W A B C 13 (some 8) (some 12) (cert (some 8) (some 12)).1 (cert (some 8) (some 12)).2=true := by decide +kernel
theorem case18 : branchCheck W A B C 13 (some 8) (some 36) (cert (some 8) (some 36)).1 (cert (some 8) (some 36)).2=true := by decide +kernel
theorem case19 : branchCheck W A B C 13 (some 8) (some 40) (cert (some 8) (some 40)).1 (cert (some 8) (some 40)).2=true := by decide +kernel
theorem case20 : branchCheck W A B C 13 (some 8) (some 46) (cert (some 8) (some 46)).1 (cert (some 8) (some 46)).2=true := by decide +kernel
theorem case21 : branchCheck W A B C 13 (some 8) (some 108) (cert (some 8) (some 108)).1 (cert (some 8) (some 108)).2=true := by decide +kernel
theorem case22 : branchCheck W A B C 13 (some 8) (some 172) (cert (some 8) (some 172)).1 (cert (some 8) (some 172)).2=true := by decide +kernel
theorem case23 : branchCheck W A B C 13 (some 8) (some 300) (cert (some 8) (some 300)).1 (cert (some 8) (some 300)).2=true := by decide +kernel
theorem case24 : branchCheck W A B C 13 (some 16) (none) (cert (some 16) (none)).1 (cert (some 16) (none)).2=true := by decide +kernel
theorem case25 : branchCheck W A B C 13 (some 16) (some 12) (cert (some 16) (some 12)).1 (cert (some 16) (some 12)).2=true := by decide +kernel
theorem case26 : branchCheck W A B C 13 (some 16) (some 36) (cert (some 16) (some 36)).1 (cert (some 16) (some 36)).2=true := by decide +kernel
theorem case27 : branchCheck W A B C 13 (some 16) (some 40) (cert (some 16) (some 40)).1 (cert (some 16) (some 40)).2=true := by decide +kernel
theorem case28 : branchCheck W A B C 13 (some 16) (some 46) (cert (some 16) (some 46)).1 (cert (some 16) (some 46)).2=true := by decide +kernel
theorem case29 : branchCheck W A B C 13 (some 16) (some 108) (cert (some 16) (some 108)).1 (cert (some 16) (some 108)).2=true := by decide +kernel
theorem case30 : branchCheck W A B C 13 (some 16) (some 172) (cert (some 16) (some 172)).1 (cert (some 16) (some 172)).2=true := by decide +kernel
theorem case31 : branchCheck W A B C 13 (some 16) (some 300) (cert (some 16) (some 300)).1 (cert (some 16) (some 300)).2=true := by decide +kernel
theorem case32 : branchCheck W A B C 13 (some 32) (none) (cert (some 32) (none)).1 (cert (some 32) (none)).2=true := by decide +kernel
theorem case33 : branchCheck W A B C 13 (some 32) (some 12) (cert (some 32) (some 12)).1 (cert (some 32) (some 12)).2=true := by decide +kernel
theorem case34 : branchCheck W A B C 13 (some 32) (some 36) (cert (some 32) (some 36)).1 (cert (some 32) (some 36)).2=true := by decide +kernel
theorem case35 : branchCheck W A B C 13 (some 32) (some 40) (cert (some 32) (some 40)).1 (cert (some 32) (some 40)).2=true := by decide +kernel
theorem case36 : branchCheck W A B C 13 (some 32) (some 46) (cert (some 32) (some 46)).1 (cert (some 32) (some 46)).2=true := by decide +kernel
theorem case37 : branchCheck W A B C 13 (some 32) (some 108) (cert (some 32) (some 108)).1 (cert (some 32) (some 108)).2=true := by decide +kernel
theorem case38 : branchCheck W A B C 13 (some 32) (some 172) (cert (some 32) (some 172)).1 (cert (some 32) (some 172)).2=true := by decide +kernel
theorem case39 : branchCheck W A B C 13 (some 32) (some 300) (cert (some 32) (some 300)).1 (cert (some 32) (some 300)).2=true := by decide +kernel
theorem case40 : branchCheck W A B C 13 (some 64) (none) (cert (some 64) (none)).1 (cert (some 64) (none)).2=true := by decide +kernel
theorem case41 : branchCheck W A B C 13 (some 64) (some 12) (cert (some 64) (some 12)).1 (cert (some 64) (some 12)).2=true := by decide +kernel
theorem case42 : branchCheck W A B C 13 (some 64) (some 36) (cert (some 64) (some 36)).1 (cert (some 64) (some 36)).2=true := by decide +kernel
theorem case43 : branchCheck W A B C 13 (some 64) (some 40) (cert (some 64) (some 40)).1 (cert (some 64) (some 40)).2=true := by decide +kernel
theorem case44 : branchCheck W A B C 13 (some 64) (some 46) (cert (some 64) (some 46)).1 (cert (some 64) (some 46)).2=true := by decide +kernel
theorem case45 : branchCheck W A B C 13 (some 64) (some 108) (cert (some 64) (some 108)).1 (cert (some 64) (some 108)).2=true := by decide +kernel
theorem case46 : branchCheck W A B C 13 (some 64) (some 172) (cert (some 64) (some 172)).1 (cert (some 64) (some 172)).2=true := by decide +kernel
theorem case47 : branchCheck W A B C 13 (some 64) (some 300) (cert (some 64) (some 300)).1 (cert (some 64) (some 300)).2=true := by decide +kernel
theorem case48 : branchCheck W A B C 13 (some 128) (none) (cert (some 128) (none)).1 (cert (some 128) (none)).2=true := by decide +kernel
theorem case49 : branchCheck W A B C 13 (some 128) (some 12) (cert (some 128) (some 12)).1 (cert (some 128) (some 12)).2=true := by decide +kernel
theorem case50 : branchCheck W A B C 13 (some 128) (some 36) (cert (some 128) (some 36)).1 (cert (some 128) (some 36)).2=true := by decide +kernel
theorem case51 : branchCheck W A B C 13 (some 128) (some 40) (cert (some 128) (some 40)).1 (cert (some 128) (some 40)).2=true := by decide +kernel
theorem case52 : branchCheck W A B C 13 (some 128) (some 46) (cert (some 128) (some 46)).1 (cert (some 128) (some 46)).2=true := by decide +kernel
theorem case53 : branchCheck W A B C 13 (some 128) (some 108) (cert (some 128) (some 108)).1 (cert (some 128) (some 108)).2=true := by decide +kernel
theorem case54 : branchCheck W A B C 13 (some 128) (some 172) (cert (some 128) (some 172)).1 (cert (some 128) (some 172)).2=true := by decide +kernel
theorem case55 : branchCheck W A B C 13 (some 128) (some 300) (cert (some 128) (some 300)).1 (cert (some 128) (some 300)).2=true := by decide +kernel
theorem case56 : branchCheck W A B C 13 (some 256) (none) (cert (some 256) (none)).1 (cert (some 256) (none)).2=true := by decide +kernel
theorem case57 : branchCheck W A B C 13 (some 256) (some 12) (cert (some 256) (some 12)).1 (cert (some 256) (some 12)).2=true := by decide +kernel
theorem case58 : branchCheck W A B C 13 (some 256) (some 36) (cert (some 256) (some 36)).1 (cert (some 256) (some 36)).2=true := by decide +kernel
theorem case59 : branchCheck W A B C 13 (some 256) (some 40) (cert (some 256) (some 40)).1 (cert (some 256) (some 40)).2=true := by decide +kernel
theorem case60 : branchCheck W A B C 13 (some 256) (some 46) (cert (some 256) (some 46)).1 (cert (some 256) (some 46)).2=true := by decide +kernel
theorem case61 : branchCheck W A B C 13 (some 256) (some 108) (cert (some 256) (some 108)).1 (cert (some 256) (some 108)).2=true := by decide +kernel
theorem case62 : branchCheck W A B C 13 (some 256) (some 172) (cert (some 256) (some 172)).1 (cert (some 256) (some 172)).2=true := by decide +kernel
theorem case63 : branchCheck W A B C 13 (some 256) (some 300) (cert (some 256) (some 300)).1 (cert (some 256) (some 300)).2=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    branchCheck W A B C 13 a b (cert a b).1 (cert a b).2))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, ⟨case05, ⟨case06, case07⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case08, ⟨case09, ⟨case10, ⟨case11, ⟨case12, ⟨case13, ⟨case14, case15⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case16, ⟨case17, ⟨case18, ⟨case19, ⟨case20, ⟨case21, ⟨case22, case23⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case24, ⟨case25, ⟨case26, ⟨case27, ⟨case28, ⟨case29, ⟨case30, case31⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case32, ⟨case33, ⟨case34, ⟨case35, ⟨case36, ⟨case37, ⟨case38, case39⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case40, ⟨case41, ⟨case42, ⟨case43, ⟨case44, ⟨case45, ⟨case46, case47⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case48, ⟨case49, ⟨case50, ⟨case51, ⟨case52, ⟨case53, ⟨case54, case55⟩⟩⟩⟩⟩⟩⟩, ⟨case56, ⟨case57, ⟨case58, ⟨case59, ⟨case60, ⟨case61, ⟨case62, case63⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    13≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  neighbour_in_snake (W:=W) (cs:=ds) (A:=A) (B:=B) (C:=C) (L:=13) (start:=6)
    cert canonical (by decide) (by decide) rfl supported pairA pairB checked p P r hr hP
#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.NeighbourChoice64.E101
