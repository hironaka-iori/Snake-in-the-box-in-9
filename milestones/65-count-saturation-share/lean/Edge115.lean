import CountChoice
namespace Snake9.LocalWindow.CountPropagation65.E115
open ForcedShare58 ExtendedShare59 SplitShare62 NeighbourChoice64
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 113, 112]
def dirs : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 0]
def A : List Nat := [4, 8, 16, 32, 64, 128, 256]
def B : List Nat := [48, 80, 96, 114, 116, 240, 368]
def C : List Nat := [27, 25, 57, 121, 113]
def bounds : List (Nat × Nat) := [(0, 21), (0, 21), (0, 21), (0, 21), (0, 1), (0, 5), (0, 21), (0, 5), (0, 1), (0, 21)]
def c0 : Centre := ⟨31,4,2,0,1⟩
def cond0 : Condition := ofCentre c0
def c1 : Centre := ⟨27,2,1,0,5⟩
def cond1 : Condition := ofCentre c1
def c2 : Centre := ⟨25,1,5,0,21⟩
def cond2 : Condition := ofCentre c2
def c3 : Centre := ⟨57,5,6,0,5⟩
def cond3 : Condition := ofCentre c3
def c4 : Centre := ⟨121,6,3,0,1⟩
def cond4 : Condition := ofCentre c4
def c5 : Centre := ⟨113,3,0,0,21⟩
def cond5 : Condition := ofCentre c5
def centres : List Centre := [c0,c1,c2,c3,c4,c5]
def conds : List Condition := centres.map ofCentre
def cert : Option Nat → Option Nat → TraceCertificate
  | none, none => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | none, some 48 => ⟨[17, 19, 33, 61, 65, 81, 89, 97], [.select cond0 [21, 87, 93], .degree [85]], .share 238345770021462447173210406912⟩
  | none, some 80 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | none, some 96 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | none, some 114 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | none, some 116 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | none, some 240 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | none, some 368 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 4, none => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 4, some 48 => ⟨[17, 19, 33, 61, 65, 81, 89, 97], [.select cond0 [21, 87, 93], .degree [85]], .share 238345770021462447173210406912⟩
  | some 4, some 80 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 4, some 96 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 4, some 114 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 4, some 116 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 4, some 240 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 4, some 368 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 8, none => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 8, some 48 => ⟨[14, 17, 19, 26, 30, 33, 61, 63, 65, 81, 89, 91, 123], [.select cond0 [21, 28, 62, 87, 93, 94, 157, 191, 223, 285, 319, 351], .select cond4 [73, 88, 107, 122, 124, 217, 251, 253, 345, 379, 381], .degree [60, 85, 90, 189, 219, 317, 347], .select cond3 [40], .degree [10], .select cond1 [75], .degree [74]], .share 1899241407420746134314501120⟩
  | some 8, some 80 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 8, some 96 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 8, some 114 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 8, some 116 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 8, some 240 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 8, some 368 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 16, none => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 16, some 48 => ⟨[17, 18, 33, 35, 61, 65, 67, 81, 89, 91, 97, 123], [.select cond0 [21, 87, 93, 94, 223, 351], .select cond4 [88, 107, 122, 217, 251, 345, 379], .degree [85, 90, 219, 347], .select cond1 [43, 75], .degree [99]], .share 872171070283151100545597571072⟩
  | some 16, some 80 => ⟨[88, 91], [], .upper cond4⟩
  | some 16, some 96 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 16, some 114 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 16, some 116 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 16, some 240 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 16, some 368 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 32, none => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 32, some 48 => ⟨[33, 40, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 32, some 80 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 32, some 96 => ⟨[91, 104], [], .upper cond4⟩
  | some 32, some 114 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 32, some 116 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 32, some 240 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 32, some 368 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 64, none => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 64, some 48 => ⟨[9, 17, 19, 33, 41, 61, 65, 81, 89, 97, 105], [.select cond0 [21, 87, 93], .degree [85]], .share 40803164977306356553193026683392⟩
  | some 64, some 80 => ⟨[88, 91], [], .upper cond4⟩
  | some 64, some 96 => ⟨[91, 104], [], .upper cond4⟩
  | some 64, some 114 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 64, some 116 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 64, some 240 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 64, some 368 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 128, none => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 128, some 48 => ⟨[17, 19, 33, 61, 65, 81, 89, 97], [.select cond0 [21, 87, 93], .degree [85]], .share 238345770021462447173210406912⟩
  | some 128, some 80 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 128, some 96 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 128, some 114 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 128, some 116 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 128, some 240 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 128, some 368 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 256, none => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 256, some 48 => ⟨[17, 19, 33, 61, 65, 81, 89, 97], [.select cond0 [21, 87, 93], .degree [85]], .share 238345770021462447173210406912⟩
  | some 256, some 80 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 256, some 96 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 256, some 114 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 256, some 116 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 256, some 240 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | some 256, some 368 => ⟨[33, 61, 63, 91], [.select cond0 [28, 62, 157, 191, 285, 319], .select cond4 [124, 253, 381], .degree [60, 189, 317]], .upper cond3⟩
  | _, _ => ⟨[],[],.share 0⟩
theorem canonical : Canon W dirs := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
theorem centres_checked : centres.all (fun c => (canonicalCentres W dirs bounds).contains c)=true := by decide +kernel
theorem case00 : certCheck W A B C conds 12 (none) (none) (cert (none) (none))=true := by decide +kernel
theorem case01 : certCheck W A B C conds 12 (none) (some 48) (cert (none) (some 48))=true := by decide +kernel
theorem case02 : certCheck W A B C conds 12 (none) (some 80) (cert (none) (some 80))=true := by decide +kernel
theorem case03 : certCheck W A B C conds 12 (none) (some 96) (cert (none) (some 96))=true := by decide +kernel
theorem case04 : certCheck W A B C conds 12 (none) (some 114) (cert (none) (some 114))=true := by decide +kernel
theorem case05 : certCheck W A B C conds 12 (none) (some 116) (cert (none) (some 116))=true := by decide +kernel
theorem case06 : certCheck W A B C conds 12 (none) (some 240) (cert (none) (some 240))=true := by decide +kernel
theorem case07 : certCheck W A B C conds 12 (none) (some 368) (cert (none) (some 368))=true := by decide +kernel
theorem case08 : certCheck W A B C conds 12 (some 4) (none) (cert (some 4) (none))=true := by decide +kernel
theorem case09 : certCheck W A B C conds 12 (some 4) (some 48) (cert (some 4) (some 48))=true := by decide +kernel
theorem case10 : certCheck W A B C conds 12 (some 4) (some 80) (cert (some 4) (some 80))=true := by decide +kernel
theorem case11 : certCheck W A B C conds 12 (some 4) (some 96) (cert (some 4) (some 96))=true := by decide +kernel
theorem case12 : certCheck W A B C conds 12 (some 4) (some 114) (cert (some 4) (some 114))=true := by decide +kernel
theorem case13 : certCheck W A B C conds 12 (some 4) (some 116) (cert (some 4) (some 116))=true := by decide +kernel
theorem case14 : certCheck W A B C conds 12 (some 4) (some 240) (cert (some 4) (some 240))=true := by decide +kernel
theorem case15 : certCheck W A B C conds 12 (some 4) (some 368) (cert (some 4) (some 368))=true := by decide +kernel
theorem case16 : certCheck W A B C conds 12 (some 8) (none) (cert (some 8) (none))=true := by decide +kernel
theorem case17 : certCheck W A B C conds 12 (some 8) (some 48) (cert (some 8) (some 48))=true := by decide +kernel
theorem case18 : certCheck W A B C conds 12 (some 8) (some 80) (cert (some 8) (some 80))=true := by decide +kernel
theorem case19 : certCheck W A B C conds 12 (some 8) (some 96) (cert (some 8) (some 96))=true := by decide +kernel
theorem case20 : certCheck W A B C conds 12 (some 8) (some 114) (cert (some 8) (some 114))=true := by decide +kernel
theorem case21 : certCheck W A B C conds 12 (some 8) (some 116) (cert (some 8) (some 116))=true := by decide +kernel
theorem case22 : certCheck W A B C conds 12 (some 8) (some 240) (cert (some 8) (some 240))=true := by decide +kernel
theorem case23 : certCheck W A B C conds 12 (some 8) (some 368) (cert (some 8) (some 368))=true := by decide +kernel
theorem case24 : certCheck W A B C conds 12 (some 16) (none) (cert (some 16) (none))=true := by decide +kernel
theorem case25 : certCheck W A B C conds 12 (some 16) (some 48) (cert (some 16) (some 48))=true := by decide +kernel
theorem case26 : certCheck W A B C conds 12 (some 16) (some 80) (cert (some 16) (some 80))=true := by decide +kernel
theorem case27 : certCheck W A B C conds 12 (some 16) (some 96) (cert (some 16) (some 96))=true := by decide +kernel
theorem case28 : certCheck W A B C conds 12 (some 16) (some 114) (cert (some 16) (some 114))=true := by decide +kernel
theorem case29 : certCheck W A B C conds 12 (some 16) (some 116) (cert (some 16) (some 116))=true := by decide +kernel
theorem case30 : certCheck W A B C conds 12 (some 16) (some 240) (cert (some 16) (some 240))=true := by decide +kernel
theorem case31 : certCheck W A B C conds 12 (some 16) (some 368) (cert (some 16) (some 368))=true := by decide +kernel
theorem case32 : certCheck W A B C conds 12 (some 32) (none) (cert (some 32) (none))=true := by decide +kernel
theorem case33 : certCheck W A B C conds 12 (some 32) (some 48) (cert (some 32) (some 48))=true := by decide +kernel
theorem case34 : certCheck W A B C conds 12 (some 32) (some 80) (cert (some 32) (some 80))=true := by decide +kernel
theorem case35 : certCheck W A B C conds 12 (some 32) (some 96) (cert (some 32) (some 96))=true := by decide +kernel
theorem case36 : certCheck W A B C conds 12 (some 32) (some 114) (cert (some 32) (some 114))=true := by decide +kernel
theorem case37 : certCheck W A B C conds 12 (some 32) (some 116) (cert (some 32) (some 116))=true := by decide +kernel
theorem case38 : certCheck W A B C conds 12 (some 32) (some 240) (cert (some 32) (some 240))=true := by decide +kernel
theorem case39 : certCheck W A B C conds 12 (some 32) (some 368) (cert (some 32) (some 368))=true := by decide +kernel
theorem case40 : certCheck W A B C conds 12 (some 64) (none) (cert (some 64) (none))=true := by decide +kernel
theorem case41 : certCheck W A B C conds 12 (some 64) (some 48) (cert (some 64) (some 48))=true := by decide +kernel
theorem case42 : certCheck W A B C conds 12 (some 64) (some 80) (cert (some 64) (some 80))=true := by decide +kernel
theorem case43 : certCheck W A B C conds 12 (some 64) (some 96) (cert (some 64) (some 96))=true := by decide +kernel
theorem case44 : certCheck W A B C conds 12 (some 64) (some 114) (cert (some 64) (some 114))=true := by decide +kernel
theorem case45 : certCheck W A B C conds 12 (some 64) (some 116) (cert (some 64) (some 116))=true := by decide +kernel
theorem case46 : certCheck W A B C conds 12 (some 64) (some 240) (cert (some 64) (some 240))=true := by decide +kernel
theorem case47 : certCheck W A B C conds 12 (some 64) (some 368) (cert (some 64) (some 368))=true := by decide +kernel
theorem case48 : certCheck W A B C conds 12 (some 128) (none) (cert (some 128) (none))=true := by decide +kernel
theorem case49 : certCheck W A B C conds 12 (some 128) (some 48) (cert (some 128) (some 48))=true := by decide +kernel
theorem case50 : certCheck W A B C conds 12 (some 128) (some 80) (cert (some 128) (some 80))=true := by decide +kernel
theorem case51 : certCheck W A B C conds 12 (some 128) (some 96) (cert (some 128) (some 96))=true := by decide +kernel
theorem case52 : certCheck W A B C conds 12 (some 128) (some 114) (cert (some 128) (some 114))=true := by decide +kernel
theorem case53 : certCheck W A B C conds 12 (some 128) (some 116) (cert (some 128) (some 116))=true := by decide +kernel
theorem case54 : certCheck W A B C conds 12 (some 128) (some 240) (cert (some 128) (some 240))=true := by decide +kernel
theorem case55 : certCheck W A B C conds 12 (some 128) (some 368) (cert (some 128) (some 368))=true := by decide +kernel
theorem case56 : certCheck W A B C conds 12 (some 256) (none) (cert (some 256) (none))=true := by decide +kernel
theorem case57 : certCheck W A B C conds 12 (some 256) (some 48) (cert (some 256) (some 48))=true := by decide +kernel
theorem case58 : certCheck W A B C conds 12 (some 256) (some 80) (cert (some 256) (some 80))=true := by decide +kernel
theorem case59 : certCheck W A B C conds 12 (some 256) (some 96) (cert (some 256) (some 96))=true := by decide +kernel
theorem case60 : certCheck W A B C conds 12 (some 256) (some 114) (cert (some 256) (some 114))=true := by decide +kernel
theorem case61 : certCheck W A B C conds 12 (some 256) (some 116) (cert (some 256) (some 116))=true := by decide +kernel
theorem case62 : certCheck W A B C conds 12 (some 256) (some 240) (cert (some 256) (some 240))=true := by decide +kernel
theorem case63 : certCheck W A B C conds 12 (some 256) (some 368) (cert (some 256) (some 368))=true := by decide +kernel
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    certCheck W A B C (centres.map ofCentre) 12 a b (cert a b)))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact ⟨⟨case00, ⟨case01, ⟨case02, ⟨case03, ⟨case04, ⟨case05, ⟨case06, case07⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case08, ⟨case09, ⟨case10, ⟨case11, ⟨case12, ⟨case13, ⟨case14, case15⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case16, ⟨case17, ⟨case18, ⟨case19, ⟨case20, ⟨case21, ⟨case22, case23⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case24, ⟨case25, ⟨case26, ⟨case27, ⟨case28, ⟨case29, ⟨case30, case31⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case32, ⟨case33, ⟨case34, ⟨case35, ⟨case36, ⟨case37, ⟨case38, case39⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case40, ⟨case41, ⟨case42, ⟨case43, ⟨case44, ⟨case45, ⟨case46, case47⟩⟩⟩⟩⟩⟩⟩, ⟨⟨case48, ⟨case49, ⟨case50, ⟨case51, ⟨case52, ⟨case53, ⟨case54, case55⟩⟩⟩⟩⟩⟩⟩, ⟨case56, ⟨case57, ⟨case58, ⟨case59, ⟨case60, ⟨case61, ⟨case62, case63⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+dirs.length≤m) (hP : ∀ j, j<dirs.length → P.fwd (dir p (r+j))=dirs.getD j 0)
    (hb : ∀ i, i<bounds.length → (bounds.getD i (0,21)).1≤coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1)≤(bounds.getD i (0,21)).2) :
    12≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  apply count_choices_in_snake (W:=W) (dirs:=dirs) (A:=A) (B:=B) (C:=C)
    (bounds:=bounds) (centres:=centres) (L:=12) (start:=6) cert canonical
    (by decide) (by decide) rfl ?_ supported pairA pairB checked p P r hr hP hb
  intro c hc
  rw [centresOf_canon canonical (by decide)]
  exact List.contains_iff.mp (List.all_eq_true.mp centres_checked c hc)

#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms centres_checked
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.CountPropagation65.E115
