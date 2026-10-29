import NeighbourChoice
namespace Snake9.LocalWindow.NeighbourChoice64.E201
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 111, 103, 101, 100]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 0]
def A : List Nat := [4, 8, 16, 32, 64, 128, 256]
def B : List Nat := [36, 68, 96, 108, 116, 228, 356]
def C : List Nat := [63, 127, 111, 103, 101]
def cert : Option Nat → Option Nat → List Nat × Nat
  | none, none => ([5, 33, 35, 37, 39, 65, 67, 69, 71, 97], 237684490992334155367476887600)
  | none, some 36 => ([5, 33, 35, 37, 39, 47, 65, 67, 68, 69, 71, 97, 99], 792281628592184659186758451248)
  | none, some 68 => ([5, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | none, some 96 => ([5, 33, 35, 36, 37, 39, 65, 67, 68, 69, 97, 99], 792281626231001277087461933104)
  | none, some 108 => ([5, 33, 35, 36, 37, 39, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | none, some 116 => ([5, 33, 35, 36, 37, 39, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | none, some 228 => ([5, 33, 35, 36, 37, 39, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | none, some 356 => ([5, 33, 35, 36, 37, 39, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 4, none => ([32, 33, 35, 37, 39, 47, 64, 65, 67, 69, 71, 79, 97, 99], 792282233055094466574360248320)
  | some 4, some 36 => ([5, 32, 33, 35, 37, 38, 39, 47, 55, 64, 65, 67, 68, 69, 96, 97, 99], 871509788745301784421671632928)
  | some 4, some 68 => ([5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 96, 97, 99], 871509790792854347600254468128)
  | some 4, some 96 => ([32, 33, 35, 36, 37, 39, 47, 64, 65, 67, 68, 69, 71, 79, 97, 99], 792282233055094466574360248320)
  | some 4, some 108 => ([32, 33, 35, 36, 37, 39, 47, 64, 65, 67, 68, 69, 71, 79, 97, 99], 792282233055094466574360248320)
  | some 4, some 116 => ([32, 33, 35, 36, 37, 39, 47, 64, 65, 67, 68, 69, 71, 79, 97, 99], 792282233055094466574360248320)
  | some 4, some 228 => ([32, 33, 35, 36, 37, 39, 47, 64, 65, 67, 68, 69, 71, 79, 97, 99], 792282233055094466574360248320)
  | some 4, some 356 => ([32, 33, 35, 36, 37, 39, 47, 64, 65, 67, 68, 69, 71, 79, 97, 99], 792282233055094466574360248320)
  | some 8, none => ([4, 5, 32, 33, 35, 37, 39, 64, 65, 67, 69, 71, 97], 237684490992334155367476887600)
  | some 8, some 36 => ([4, 5, 33, 35, 37, 39, 47, 64, 65, 67, 68, 69, 71, 97, 99], 792281628592184659186758451248)
  | some 8, some 68 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 8, some 96 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 97, 99], 792281626231001277087461933104)
  | some 8, some 108 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 8, some 116 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 8, some 228 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 8, some 356 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 16, none => ([4, 5, 32, 33, 35, 37, 39, 64, 65, 67, 69, 71, 97], 237684490992334155367476887600)
  | some 16, some 36 => ([4, 5, 33, 35, 37, 39, 47, 64, 65, 67, 68, 69, 71, 97, 99], 792281628592184659186758451248)
  | some 16, some 68 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 16, some 96 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 97, 99], 792281626231001277087461933104)
  | some 16, some 108 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 16, some 116 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 16, some 228 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 16, some 356 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 32, none => ([4, 5, 33, 35, 37, 39, 64, 65, 67, 69, 71, 97, 99], 792281628592184518517989572656)
  | some 32, some 36 => ([4, 5, 33, 34, 35, 37, 38, 39, 47, 55, 64, 65, 67, 68, 69, 97, 99], 792281626231037446841012584496)
  | some 32, some 68 => ([4, 5, 33, 35, 36, 37, 39, 47, 64, 65, 67, 69, 71, 96, 97, 99], 871509790811301091669669052464)
  | some 32, some 96 => ([4, 5, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 97, 99], 792281628592184518517989572656)
  | some 32, some 108 => ([4, 5, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 97, 99], 792281628592184518517989572656)
  | some 32, some 116 => ([4, 5, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 97, 99], 792281628592184518517989572656)
  | some 32, some 228 => ([4, 5, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 97, 99], 792281628592184518517989572656)
  | some 32, some 356 => ([4, 5, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 97, 99], 792281628592184518517989572656)
  | some 64, none => ([4, 5, 32, 33, 35, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 64, some 36 => ([4, 5, 32, 33, 35, 37, 39, 47, 65, 67, 68, 69, 71, 96, 97, 99], 871509791088002252710887817264)
  | some 64, some 68 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 64, some 96 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 64, some 108 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 64, some 116 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 64, some 228 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 64, some 356 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 128, none => ([4, 5, 32, 33, 35, 37, 39, 64, 65, 67, 69, 71, 97], 237684490992334155367476887600)
  | some 128, some 36 => ([4, 5, 33, 35, 37, 39, 47, 64, 65, 67, 68, 69, 71, 97, 99], 792281628592184659186758451248)
  | some 128, some 68 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 128, some 96 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 97, 99], 792281626231001277087461933104)
  | some 128, some 108 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 128, some 116 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 128, some 228 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 128, some 356 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 256, none => ([4, 5, 32, 33, 35, 37, 39, 64, 65, 67, 69, 71, 97], 237684490992334155367476887600)
  | some 256, some 36 => ([4, 5, 33, 35, 37, 39, 47, 64, 65, 67, 68, 69, 71, 97, 99], 792281628592184659186758451248)
  | some 256, some 68 => ([4, 5, 32, 33, 35, 36, 37, 39, 47, 65, 67, 69, 71, 97, 99], 792281628278590010006710517808)
  | some 256, some 96 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 97, 99], 792281626231001277087461933104)
  | some 256, some 108 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 256, some 116 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 256, some 228 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | some 256, some 356 => ([4, 5, 32, 33, 35, 36, 37, 39, 64, 65, 67, 68, 69, 71, 96, 97], 237684490992334155367476887600)
  | _, _ => ([],0)
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem case00 : branchCheck W A B C 20 (none) (none) (cert (none) (none)).1 (cert (none) (none)).2=true := by decide +kernel
theorem case01 : branchCheck W A B C 20 (none) (some 36) (cert (none) (some 36)).1 (cert (none) (some 36)).2=true := by decide +kernel
theorem case02 : branchCheck W A B C 20 (none) (some 68) (cert (none) (some 68)).1 (cert (none) (some 68)).2=true := by decide +kernel
theorem case03 : branchCheck W A B C 20 (none) (some 96) (cert (none) (some 96)).1 (cert (none) (some 96)).2=true := by decide +kernel
theorem case04 : branchCheck W A B C 20 (none) (some 108) (cert (none) (some 108)).1 (cert (none) (some 108)).2=true := by decide +kernel
theorem case05 : branchCheck W A B C 20 (none) (some 116) (cert (none) (some 116)).1 (cert (none) (some 116)).2=true := by decide +kernel
theorem case06 : branchCheck W A B C 20 (none) (some 228) (cert (none) (some 228)).1 (cert (none) (some 228)).2=true := by decide +kernel
theorem case07 : branchCheck W A B C 20 (none) (some 356) (cert (none) (some 356)).1 (cert (none) (some 356)).2=true := by decide +kernel
theorem case08 : branchCheck W A B C 20 (some 4) (none) (cert (some 4) (none)).1 (cert (some 4) (none)).2=true := by decide +kernel
theorem case09 : branchCheck W A B C 20 (some 4) (some 36) (cert (some 4) (some 36)).1 (cert (some 4) (some 36)).2=true := by decide +kernel
theorem case10 : branchCheck W A B C 20 (some 4) (some 68) (cert (some 4) (some 68)).1 (cert (some 4) (some 68)).2=true := by decide +kernel
theorem case11 : branchCheck W A B C 20 (some 4) (some 96) (cert (some 4) (some 96)).1 (cert (some 4) (some 96)).2=true := by decide +kernel
theorem case12 : branchCheck W A B C 20 (some 4) (some 108) (cert (some 4) (some 108)).1 (cert (some 4) (some 108)).2=true := by decide +kernel
theorem case13 : branchCheck W A B C 20 (some 4) (some 116) (cert (some 4) (some 116)).1 (cert (some 4) (some 116)).2=true := by decide +kernel
theorem case14 : branchCheck W A B C 20 (some 4) (some 228) (cert (some 4) (some 228)).1 (cert (some 4) (some 228)).2=true := by decide +kernel
theorem case15 : branchCheck W A B C 20 (some 4) (some 356) (cert (some 4) (some 356)).1 (cert (some 4) (some 356)).2=true := by decide +kernel
theorem case16 : branchCheck W A B C 20 (some 8) (none) (cert (some 8) (none)).1 (cert (some 8) (none)).2=true := by decide +kernel
theorem case17 : branchCheck W A B C 20 (some 8) (some 36) (cert (some 8) (some 36)).1 (cert (some 8) (some 36)).2=true := by decide +kernel
theorem case18 : branchCheck W A B C 20 (some 8) (some 68) (cert (some 8) (some 68)).1 (cert (some 8) (some 68)).2=true := by decide +kernel
theorem case19 : branchCheck W A B C 20 (some 8) (some 96) (cert (some 8) (some 96)).1 (cert (some 8) (some 96)).2=true := by decide +kernel
theorem case20 : branchCheck W A B C 20 (some 8) (some 108) (cert (some 8) (some 108)).1 (cert (some 8) (some 108)).2=true := by decide +kernel
theorem case21 : branchCheck W A B C 20 (some 8) (some 116) (cert (some 8) (some 116)).1 (cert (some 8) (some 116)).2=true := by decide +kernel
theorem case22 : branchCheck W A B C 20 (some 8) (some 228) (cert (some 8) (some 228)).1 (cert (some 8) (some 228)).2=true := by decide +kernel
theorem case23 : branchCheck W A B C 20 (some 8) (some 356) (cert (some 8) (some 356)).1 (cert (some 8) (some 356)).2=true := by decide +kernel
theorem case24 : branchCheck W A B C 20 (some 16) (none) (cert (some 16) (none)).1 (cert (some 16) (none)).2=true := by decide +kernel
theorem case25 : branchCheck W A B C 20 (some 16) (some 36) (cert (some 16) (some 36)).1 (cert (some 16) (some 36)).2=true := by decide +kernel
theorem case26 : branchCheck W A B C 20 (some 16) (some 68) (cert (some 16) (some 68)).1 (cert (some 16) (some 68)).2=true := by decide +kernel
theorem case27 : branchCheck W A B C 20 (some 16) (some 96) (cert (some 16) (some 96)).1 (cert (some 16) (some 96)).2=true := by decide +kernel
theorem case28 : branchCheck W A B C 20 (some 16) (some 108) (cert (some 16) (some 108)).1 (cert (some 16) (some 108)).2=true := by decide +kernel
theorem case29 : branchCheck W A B C 20 (some 16) (some 116) (cert (some 16) (some 116)).1 (cert (some 16) (some 116)).2=true := by decide +kernel
theorem case30 : branchCheck W A B C 20 (some 16) (some 228) (cert (some 16) (some 228)).1 (cert (some 16) (some 228)).2=true := by decide +kernel
theorem case31 : branchCheck W A B C 20 (some 16) (some 356) (cert (some 16) (some 356)).1 (cert (some 16) (some 356)).2=true := by decide +kernel
theorem case32 : branchCheck W A B C 20 (some 32) (none) (cert (some 32) (none)).1 (cert (some 32) (none)).2=true := by decide +kernel
theorem case33 : branchCheck W A B C 20 (some 32) (some 36) (cert (some 32) (some 36)).1 (cert (some 32) (some 36)).2=true := by decide +kernel
theorem case34 : branchCheck W A B C 20 (some 32) (some 68) (cert (some 32) (some 68)).1 (cert (some 32) (some 68)).2=true := by decide +kernel
theorem case35 : branchCheck W A B C 20 (some 32) (some 96) (cert (some 32) (some 96)).1 (cert (some 32) (some 96)).2=true := by decide +kernel
theorem case36 : branchCheck W A B C 20 (some 32) (some 108) (cert (some 32) (some 108)).1 (cert (some 32) (some 108)).2=true := by decide +kernel
theorem case37 : branchCheck W A B C 20 (some 32) (some 116) (cert (some 32) (some 116)).1 (cert (some 32) (some 116)).2=true := by decide +kernel
theorem case38 : branchCheck W A B C 20 (some 32) (some 228) (cert (some 32) (some 228)).1 (cert (some 32) (some 228)).2=true := by decide +kernel
theorem case39 : branchCheck W A B C 20 (some 32) (some 356) (cert (some 32) (some 356)).1 (cert (some 32) (some 356)).2=true := by decide +kernel
theorem case40 : branchCheck W A B C 20 (some 64) (none) (cert (some 64) (none)).1 (cert (some 64) (none)).2=true := by decide +kernel
theorem case41 : branchCheck W A B C 20 (some 64) (some 36) (cert (some 64) (some 36)).1 (cert (some 64) (some 36)).2=true := by decide +kernel
theorem case42 : branchCheck W A B C 20 (some 64) (some 68) (cert (some 64) (some 68)).1 (cert (some 64) (some 68)).2=true := by decide +kernel
theorem case43 : branchCheck W A B C 20 (some 64) (some 96) (cert (some 64) (some 96)).1 (cert (some 64) (some 96)).2=true := by decide +kernel
theorem case44 : branchCheck W A B C 20 (some 64) (some 108) (cert (some 64) (some 108)).1 (cert (some 64) (some 108)).2=true := by decide +kernel
theorem case45 : branchCheck W A B C 20 (some 64) (some 116) (cert (some 64) (some 116)).1 (cert (some 64) (some 116)).2=true := by decide +kernel
theorem case46 : branchCheck W A B C 20 (some 64) (some 228) (cert (some 64) (some 228)).1 (cert (some 64) (some 228)).2=true := by decide +kernel
theorem case47 : branchCheck W A B C 20 (some 64) (some 356) (cert (some 64) (some 356)).1 (cert (some 64) (some 356)).2=true := by decide +kernel
theorem case48 : branchCheck W A B C 20 (some 128) (none) (cert (some 128) (none)).1 (cert (some 128) (none)).2=true := by decide +kernel
theorem case49 : branchCheck W A B C 20 (some 128) (some 36) (cert (some 128) (some 36)).1 (cert (some 128) (some 36)).2=true := by decide +kernel
theorem case50 : branchCheck W A B C 20 (some 128) (some 68) (cert (some 128) (some 68)).1 (cert (some 128) (some 68)).2=true := by decide +kernel
theorem case51 : branchCheck W A B C 20 (some 128) (some 96) (cert (some 128) (some 96)).1 (cert (some 128) (some 96)).2=true := by decide +kernel
theorem case52 : branchCheck W A B C 20 (some 128) (some 108) (cert (some 128) (some 108)).1 (cert (some 128) (some 108)).2=true := by decide +kernel
theorem case53 : branchCheck W A B C 20 (some 128) (some 116) (cert (some 128) (some 116)).1 (cert (some 128) (some 116)).2=true := by decide +kernel
theorem case54 : branchCheck W A B C 20 (some 128) (some 228) (cert (some 128) (some 228)).1 (cert (some 128) (some 228)).2=true := by decide +kernel
theorem case55 : branchCheck W A B C 20 (some 128) (some 356) (cert (some 128) (some 356)).1 (cert (some 128) (some 356)).2=true := by decide +kernel
theorem case56 : branchCheck W A B C 20 (some 256) (none) (cert (some 256) (none)).1 (cert (some 256) (none)).2=true := by decide +kernel
theorem case57 : branchCheck W A B C 20 (some 256) (some 36) (cert (some 256) (some 36)).1 (cert (some 256) (some 36)).2=true := by decide +kernel
theorem case58 : branchCheck W A B C 20 (some 256) (some 68) (cert (some 256) (some 68)).1 (cert (some 256) (some 68)).2=true := by decide +kernel
theorem case59 : branchCheck W A B C 20 (some 256) (some 96) (cert (some 256) (some 96)).1 (cert (some 256) (some 96)).2=true := by decide +kernel
theorem case60 : branchCheck W A B C 20 (some 256) (some 108) (cert (some 256) (some 108)).1 (cert (some 256) (some 108)).2=true := by decide +kernel
theorem case61 : branchCheck W A B C 20 (some 256) (some 116) (cert (some 256) (some 116)).1 (cert (some 256) (some 116)).2=true := by decide +kernel
theorem case62 : branchCheck W A B C 20 (some 256) (some 228) (cert (some 256) (some 228)).1 (cert (some 256) (some 228)).2=true := by decide +kernel
theorem case63 : branchCheck W A B C 20 (some 256) (some 356) (cert (some 256) (some 356)).1 (cert (some 256) (some 356)).2=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    branchCheck W A B C 20 a b (cert a b).1 (cert a b).2))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, ⟨case05, ⟨case06, case07⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case08, ⟨case09, ⟨case10, ⟨case11, ⟨case12, ⟨case13, ⟨case14, case15⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case16, ⟨case17, ⟨case18, ⟨case19, ⟨case20, ⟨case21, ⟨case22, case23⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case24, ⟨case25, ⟨case26, ⟨case27, ⟨case28, ⟨case29, ⟨case30, case31⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case32, ⟨case33, ⟨case34, ⟨case35, ⟨case36, ⟨case37, ⟨case38, case39⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case40, ⟨case41, ⟨case42, ⟨case43, ⟨case44, ⟨case45, ⟨case46, case47⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case48, ⟨case49, ⟨case50, ⟨case51, ⟨case52, ⟨case53, ⟨case54, case55⟩⟩⟩⟩⟩⟩⟩, ⟨case56, ⟨case57, ⟨case58, ⟨case59, ⟨case60, ⟨case61, ⟨case62, case63⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    20≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  neighbour_in_snake (W:=W) (cs:=ds) (A:=A) (B:=B) (C:=C) (L:=20) (start:=6)
    cert canonical (by decide) (by decide) rfl supported pairA pairB checked p P r hr hP
#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.NeighbourChoice64.E201
