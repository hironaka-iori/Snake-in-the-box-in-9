import PartitionData205_198
import PartitionPiece205_198_0
import PartitionPiece205_198_1
import PartitionPiece205_198_2
import PartitionPiece205_198_3
import PartitionPiece205_198_4
namespace PartitionCover205_198
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1,2,3,4,5])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2])
    (start6 : a 6 ∈ [0,1,2])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start14 : a 14 ∈ [0,1,2])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (start16 : a 16 ∈ [0,1,2,3,4,5])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start27 : a 27 ∈ [0,1,2])
    (start28 : a 28 ∈ [0,1,2,3])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
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
      (a 0=0 ∧ a 1=0 ∧ a 2=1 ∧ a 3=1 ∧ a 4=2 ∧ a 5=2 ∧ a 6=0 ∧ a 7=1 ∧ a 8=1 ∧ a 9=1 ∧ a 10=2 ∧ a 11=1 ∧ a 12=1 ∧ a 13=4 ∧ a 14=0 ∧ a 15=1 ∧ a 16=3 ∧ a 17=6 ∧ a 18=0 ∧ a 19=1 ∧ a 20=0 ∧ a 21=6 ∧ a 22=3 ∧ a 23=1 ∧ a 24=6 ∧ a 25=1 ∧ a 26=4 ∧ a 27=1 ∧ a 28=0 ∧ a 29=6 ∧ a 30=4 ∧ a 31=1) := by
  have group1 := chunk0 a start2 start0 start4 start16 start17 start1 c1 c2 c4 c8
  rcases group1 with ⟨h2,h3,h4,h5⟩
  have group6 := chunk1 a h5 start1 start3 h2 start6 start10 start18 c8 c9 c10 c11 c12
  rcases group6 with ⟨h7,h8,h9,h10,h11⟩
  have group12 := chunk2 a h11 h2 start7 h8 start11 c12 c13 c14
  rcases group12 with ⟨h13,h14,h15⟩
  have group16 := chunk3 a h15 h8 start5 h3 start12 start20 start13 start14 h9 c14 c16 c18 c19 c21 c24
  rcases group16 with ⟨h17,h18,h19,h20,h21,h22⟩
  have group23 := chunk4 a h22 h9 start22 start15 h14 start9 start8 h10 c24 c25 c26 c28 c29
  rcases group23 with ⟨h24,h25,h26,h27,h28⟩
  have group29 := chunk5 a h28 start8 h27 h17 h21 start25 start26 c29 c32 c33 c34 c37
  rcases group29 with ⟨h30,h31,h32,h33,h34⟩
  have group35 := chunk6 a h34 h30 h26 h17 start27 start28 h19 start29 h32 c37 c38 c39 c42 c44
  rcases group35 with ⟨h36,h37,h38,h39,h40⟩
  have group41 := chunk7 a h40 h32 start31 h37 h7 h4 start24 c44 c47 c48 c51
  rcases group41 with ⟨h42,h43,h44,h45⟩
  have group46 := chunk8 a h45 h4 start21 h44 start19 h13 c51 c53 c55
  rcases group46 with ⟨h47,h48,h49⟩
  have group50 := chunk9 a h49 h13 c55
  have h51 := group50
  have group52 := chunk10 a h51 h13 h36 start23 c55 c57 c58
  rcases group52 with ⟨h53,h54,h55,h56⟩
  have group57 := chunk11 a h56 h53 h20 h48 h39 h42 start30 h25 c58 c60 c62 c64 c66
  rcases group57 with ⟨h58,h59,h60,h61,h62⟩
  have group63 := chunk12 a h62 h25 h58 h43 c66 c67
  rcases group63 with ⟨h64,h65,h66⟩
  have group67 := chunk13 a h66 h65 h47 h33 h64 h55 h32 h61 h53 h54 c44 c55 c67 c68 c74
  rcases group67 with ⟨h68,h69,h70,h71,h72⟩
  rcases (show a 2=0 ∨ a 2=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h2) with q73 | q74
  · have h75 : a 2 ∈ [0] := List.mem_singleton.mpr q73
    have group76 := chunk14 a h8 h75 h30 h14 h17 h18 h71 h48 h37 start8 h19 h69 h31 h55 h38 h4 h44 c9 c11 c13 c14 c20 c21 c22 c26 c29 c30 c31 c32 c37 c39 c51 c53
    rcases group76 with ⟨h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91,h92⟩
    have group93 := chunk15 a h72 h90 h61 h83 h33 h87 h70 h89 h68 h3 h81 h65 h25 c16 c58 c59 c64 c65 c68 c74 c75
    rcases group93 with ⟨h94,h95,h96,h97,h98,h99,h100,h101⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h75) (And.intro (forced (a 3) 0 h77) (And.intro (forced (a 4) 0 h99) (And.intro (forced (a 5) 0 h81) (And.intro (forced (a 6) 0 h9) (And.intro (forced (a 7) 0 h79) (And.intro (forced (a 8) 0 h85) (And.intro (forced (a 9) 0 h88) (And.intro (forced (a 10) 0 h78) (And.intro (forced (a 11) 0 h80) (And.intro (forced (a 12) 0 h86) (And.intro (forced (a 13) 0 h82) (And.intro (forced (a 14) 0 h24) (And.intro (forced (a 15) 0 h84) (And.intro (forced (a 16) 0 h91) (And.intro (forced (a 17) 0 h92) (And.intro (forced (a 18) 0 h54) (And.intro (forced (a 19) 0 h94) (And.intro (forced (a 20) 0 h59) (And.intro (forced (a 21) 0 h83) (And.intro (forced (a 22) 0 h101) (And.intro (forced (a 23) 0 h100) (And.intro (forced (a 24) 0 h87) (And.intro (forced (a 25) 0 h96) (And.intro (forced (a 26) 0 h89) (And.intro (forced (a 27) 0 h90) (And.intro (forced (a 28) 0 h60) (And.intro (forced (a 29) 0 h95) (And.intro (forced (a 30) 0 h97) (forced (a 31) 0 h98))))))))))))))))))))))))))))))))
  · have h102 : a 2 ∈ [1] := List.mem_singleton.mpr q74
    have group103 := chunk16 a h8 h102 h30 h14 h17 h18 h71 h48 h37 start8 h19 h69 h31 h55 h38 h4 h44 c9 c11 c13 c14 c20 c21 c22 c26 c29 c30 c31 c32 c37 c39 c51 c53
    rcases group103 with ⟨h104,h105,h106,h107,h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119⟩
    have group120 := chunk17 a h72 h117 h61 h110 h33 h114 h70 h116 h68 h3 h108 h65 h25 c16 c58 c59 c64 c65 c68 c74 c75
    rcases group120 with ⟨h121,h122,h123,h124,h125,h126,h127,h128⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 1 h102) (And.intro (forced (a 3) 1 h104) (And.intro (forced (a 4) 2 h126) (And.intro (forced (a 5) 2 h108) (And.intro (forced (a 6) 0 h9) (And.intro (forced (a 7) 1 h106) (And.intro (forced (a 8) 1 h112) (And.intro (forced (a 9) 1 h115) (And.intro (forced (a 10) 2 h105) (And.intro (forced (a 11) 1 h107) (And.intro (forced (a 12) 1 h113) (And.intro (forced (a 13) 4 h109) (And.intro (forced (a 14) 0 h24) (And.intro (forced (a 15) 1 h111) (And.intro (forced (a 16) 3 h118) (And.intro (forced (a 17) 6 h119) (And.intro (forced (a 18) 0 h54) (And.intro (forced (a 19) 1 h121) (And.intro (forced (a 20) 0 h59) (And.intro (forced (a 21) 6 h110) (And.intro (forced (a 22) 3 h128) (And.intro (forced (a 23) 1 h127) (And.intro (forced (a 24) 6 h114) (And.intro (forced (a 25) 1 h123) (And.intro (forced (a 26) 4 h116) (And.intro (forced (a 27) 1 h117) (And.intro (forced (a 28) 0 h60) (And.intro (forced (a 29) 6 h122) (And.intro (forced (a 30) 4 h124) (forced (a 31) 1 h125))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_198
