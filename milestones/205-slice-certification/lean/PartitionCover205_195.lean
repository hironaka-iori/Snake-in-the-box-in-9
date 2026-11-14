import PartitionData205_195
import PartitionPiece205_195_0
import PartitionPiece205_195_1
import PartitionPiece205_195_2
import PartitionPiece205_195_3
namespace PartitionCover205_195
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3])
    (start3 : a 3 ∈ [0,1,2,3])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0,1,2,3])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1,2])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1,2,3])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start17 : a 17 ∈ [0,1,2,3,4,5])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start20 : a 20 ∈ [0,1])
    (start21 : a 21 ∈ [0,1])
    (start22 : a 22 ∈ [0,1,2,3])
    (start23 : a 23 ∈ [0,1,2,3])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7])
    (start31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0) ∨
      (a 0=0 ∧ a 1=1 ∧ a 2=2 ∧ a 3=2 ∧ a 4=1 ∧ a 5=1 ∧ a 6=1 ∧ a 7=2 ∧ a 8=1 ∧ a 9=2 ∧ a 10=3 ∧ a 11=6 ∧ a 12=1 ∧ a 13=1 ∧ a 14=2 ∧ a 15=2 ∧ a 16=12 ∧ a 17=3 ∧ a 18=5 ∧ a 19=3 ∧ a 20=1 ∧ a 21=1 ∧ a 22=2 ∧ a 23=2 ∧ a 24=8 ∧ a 25=9 ∧ a 26=2 ∧ a 27=2 ∧ a 28=7 ∧ a 29=4 ∧ a 30=4 ∧ a 31=9) := by
  have group1 := chunk0 a start2 start0 start16 start9 start1 start3 c1 c4 c7 c9
  rcases group1 with ⟨h2,h3,h4,h5⟩
  have group6 := chunk1 a h5 h2 start10 start18 start7 start11 start19 c9 c11 c12 c13 c14 c15
  rcases group6 with ⟨h7,h8,h9,h10,h11,h12⟩
  have group13 := chunk2 a h12 h7 start14 start6 start23 h10 start24 start8 start25 h4 c15 c24 c27 c31 c34
  rcases group13 with ⟨h14,h15,h16,h17,h18⟩
  have group19 := chunk3 a h18 h4 h11 h8 start26 start27 c34 c35 c37 c39
  rcases group19 with ⟨h20,h21,h22,h23⟩
  have group24 := chunk4 a h23 h21 start28 start12 start29 start13 c39 c42 c44
  rcases group24 with ⟨h25,h26,h27⟩
  have group28 := chunk5 a h27 start13 start15 h15 start30 start31 c44 c45 c46 c47
  rcases group28 with ⟨h29,h30,h31,h32⟩
  have group33 := chunk6 a h32 h30 start17 h3 h17 start21 h14 h9 start22 h22 c47 c48 c51 c53 c55 c56 c57
  rcases group33 with ⟨h34,h35,h36,h37,h38,h39⟩
  have group40 := chunk7 a h39 h9 h37 h16 h25 h26 start20 h34 h20 h17 c57 c58 c59 c62 c67 c68
  rcases group40 with ⟨h41,h42,h43,h44,h45⟩
  have group46 := chunk8 a h45 h17 h41 h29 h25 c68 c69 c72 c73
  rcases group46 with ⟨h47,h48,h49,h50,h51⟩
  have group52 := chunk9 a h51 h49 h44 h31 h43 h36 h48 h9 h42 c51 c55 c73 c75 c77
  rcases group52 with ⟨h53,h54,h55,h56,h57⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q58 | q59
  · have h60 : a 1 ∈ [0] := List.mem_singleton.mpr q58
    have group61 := chunk10 a h7 h60 start5 h4 h35 h2 start6 h8 start4 start12 h10 start13 start21 h15 h38 start8 h48 c5 c6 c7 c8 c9 c10 c11 c17 c18 c20 c21 c22 c24 c25 c28 c31
    rcases group61 with ⟨h62,h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75,h76,h77⟩
    have group78 := chunk11 a h21 h68 h49 h43 h70 h30 h72 h50 h55 h74 h54 h56 h65 h57 h75 start20 h73 h16 h47 h77 h53 h42 c35 c37 c42 c43 c44 c46 c47 c48 c55 c56 c60 c63 c68 c73
    rcases group78 with ⟨h79,h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91,h92⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h60) (And.intro (forced (a 2) 0 h66) (And.intro (forced (a 3) 0 h62) (And.intro (forced (a 4) 0 h69) (And.intro (forced (a 5) 0 h63) (And.intro (forced (a 6) 0 h67) (And.intro (forced (a 7) 0 h71) (And.intro (forced (a 8) 0 h76) (And.intro (forced (a 9) 0 h64) (And.intro (forced (a 10) 0 h68) (And.intro (forced (a 11) 0 h79) (And.intro (forced (a 12) 0 h70) (And.intro (forced (a 13) 0 h72) (And.intro (forced (a 14) 0 h74) (And.intro (forced (a 15) 0 h82) (And.intro (forced (a 16) 0 h86) (And.intro (forced (a 17) 0 h65) (And.intro (forced (a 18) 0 h87) (And.intro (forced (a 19) 0 h92) (And.intro (forced (a 20) 0 h88) (And.intro (forced (a 21) 0 h73) (And.intro (forced (a 22) 0 h75) (And.intro (forced (a 23) 0 h89) (And.intro (forced (a 24) 0 h77) (And.intro (forced (a 25) 0 h90) (And.intro (forced (a 26) 0 h80) (And.intro (forced (a 27) 0 h91) (And.intro (forced (a 28) 0 h81) (And.intro (forced (a 29) 0 h83) (And.intro (forced (a 30) 0 h84) (forced (a 31) 0 h85))))))))))))))))))))))))))))))))
  · have h93 : a 1 ∈ [1] := List.mem_singleton.mpr q59
    have group94 := chunk12 a h7 h93 start5 h4 h35 h2 start6 h8 start4 start12 h10 start13 start21 h15 h38 start8 h48 c5 c6 c7 c8 c9 c10 c11 c17 c18 c20 c21 c22 c24 c25 c28 c31
    rcases group94 with ⟨h95,h96,h97,h98,h99,h100,h101,h102,h103,h104,h105,h106,h107,h108,h109,h110⟩
    have group111 := chunk13 a h21 h101 h49 h43 h103 h30 h105 h50 h55 h107 h54 h56 h98 h57 h108 start20 h106 h16 h47 h110 h53 h42 c35 c37 c42 c43 c44 c46 c47 c48 c55 c56 c60 c63 c68 c73
    rcases group111 with ⟨h112,h113,h114,h115,h116,h117,h118,h119,h120,h121,h122,h123,h124,h125⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h93) (And.intro (forced (a 2) 2 h99) (And.intro (forced (a 3) 2 h95) (And.intro (forced (a 4) 1 h102) (And.intro (forced (a 5) 1 h96) (And.intro (forced (a 6) 1 h100) (And.intro (forced (a 7) 2 h104) (And.intro (forced (a 8) 1 h109) (And.intro (forced (a 9) 2 h97) (And.intro (forced (a 10) 3 h101) (And.intro (forced (a 11) 6 h112) (And.intro (forced (a 12) 1 h103) (And.intro (forced (a 13) 1 h105) (And.intro (forced (a 14) 2 h107) (And.intro (forced (a 15) 2 h115) (And.intro (forced (a 16) 12 h119) (And.intro (forced (a 17) 3 h98) (And.intro (forced (a 18) 5 h120) (And.intro (forced (a 19) 3 h125) (And.intro (forced (a 20) 1 h121) (And.intro (forced (a 21) 1 h106) (And.intro (forced (a 22) 2 h108) (And.intro (forced (a 23) 2 h122) (And.intro (forced (a 24) 8 h110) (And.intro (forced (a 25) 9 h123) (And.intro (forced (a 26) 2 h113) (And.intro (forced (a 27) 2 h124) (And.intro (forced (a 28) 7 h114) (And.intro (forced (a 29) 4 h116) (And.intro (forced (a 30) 4 h117) (forced (a 31) 9 h118))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_195
