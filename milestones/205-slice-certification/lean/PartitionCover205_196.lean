import PartitionData205_196
import PartitionPiece205_196_0
import PartitionPiece205_196_1
import PartitionPiece205_196_2
import PartitionPiece205_196_3
import PartitionPiece205_196_4
namespace PartitionCover205_196
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2])
    (start3 : a 3 ∈ [0,1,2])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8])
    (start6 : a 6 ∈ [0,1,2,3,4,5])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1,2,3,4,5])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start14 : a 14 ∈ [0,1,2,3,4,5])
    (start15 : a 15 ∈ [0,1,2,3,4,5])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8])
    (start18 : a 18 ∈ [0,1,2,3])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8])
    (start20 : a 20 ∈ [0,1,2])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2])
    (start23 : a 23 ∈ [0,1,2,3,4,5])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=0 ∧ a 3=2 ∧ a 4=1 ∧ a 5=3 ∧ a 6=1 ∧ a 7=1 ∧ a 8=2 ∧ a 9=2 ∧ a 10=1 ∧ a 11=4 ∧ a 12=2 ∧ a 13=2 ∧ a 14=2 ∧ a 15=1 ∧ a 16=3 ∧ a 17=3 ∧ a 18=3 ∧ a 19=3 ∧ a 20=0 ∧ a 21=1 ∧ a 22=1 ∧ a 23=1 ∧ a 24=6 ∧ a 25=0 ∧ a 26=12 ∧ a 27=0 ∧ a 28=2 ∧ a 29=1 ∧ a 30=6 ∧ a 31=1) := by
  have group1 := chunk0 a start4 start0 start8 start16 start3 start1 start5 c2 c3 c4 c5 c6
  rcases group1 with ⟨h2,h3,h4,h5,h6⟩
  have group7 := chunk1 a h6 start1 start9 start17 start18 start2 start11 h5 c6 c7 c8 c12 c14
  rcases group7 with ⟨h8,h9,h10,h11,h12⟩
  have group13 := chunk2 a h12 h5 start19 start6 h2 start12 start7 h8 c14 c15 c17 c18 c20
  rcases group13 with ⟨h14,h15,h16,h17,h18⟩
  have group19 := chunk3 a h18 h8 start13 start21 start14 h16 c20 c21 c22 c24
  rcases group19 with ⟨h20,h21,h22,h23⟩
  have group24 := chunk4 a h23 h16 start22 start15 h20 start23 h3 h9 start10 start24 c24 c25 c26 c27 c28 c29 c31
  rcases group24 with ⟨h25,h26,h27,h28,h29,h30,h31⟩
  have group32 := chunk5 a h31 h29 h14 h9 start25 c31 c32 c34
  rcases group32 with ⟨h33,h34,h35⟩
  have group36 := chunk6 a h35 h9 h30 h34 h25 start26 c34 c35 c36 c37
  rcases group36 with ⟨h37,h38,h39,h40,h41⟩
  have group42 := chunk7 a h41 h38 start27 h39 h17 h21 start28 c37 c39 c40 c42
  rcases group42 with ⟨h43,h44,h45,h46⟩
  have group47 := chunk8 a h46 h45 c42
  have h48 := group47
  have group49 := chunk9 a h48 h45 h27 h21 start29 c42 c43 c44
  rcases group49 with ⟨h50,h51,h52⟩
  have group53 := chunk10 a h52 h21 start30 h40 start31 h51 c44 c46 c47
  rcases group53 with ⟨h54,h55,h56⟩
  have group57 := chunk11 a h56 h51 h11 h4 start20 h33 h15 h10 h43 c47 c49 c50 c51 c52 c57
  rcases group57 with ⟨h58,h59,h60,h61,h62,h63⟩
  have group64 := chunk12 a h63 h59 h44 h62 h28 h22 h55 h26 h58 c57 c59 c63 c66 c67
  rcases group64 with ⟨h65,h66,h67,h68,h69⟩
  have group70 := chunk13 a h69 h67 h37 h61 h65 h66 c67 c68 c69 c73 c75
  rcases group70 with ⟨h71,h72,h73⟩
  have group74 := chunk14 a h71 h66 h50 h54 h68 h16 h40 h20 h51 start2 h2 c10 c17 c24 c26 c75 c76 c77 c78
  rcases group74 with ⟨h75,h76,h77,h78,h79,h80,h81,h82⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q83 | q84
  · have h85 : a 1 ∈ [0] := List.mem_singleton.mpr q83
    have group86 := chunk15 a h8 h85 h9 h82 h79 h45 h80 h21 h22 h40 h26 h51 h67 h29 h38 h61 h39 c6 c7 c16 c17 c18 c20 c21 c22 c24 c25 c26 c27 c28 c29 c31 c32
    rcases group86 with ⟨h87,h88,h89,h90,h91,h92,h93,h94,h95,h96,h97,h98,h99,h100,h101,h102⟩
    have group103 := chunk16 a h73 h100 h76 h91 h78 h93 h77 h95 h4 h101 h59 h62 h98 h75 h5 h102 h10 c14 c37 c42 c44 c46 c48 c51 c57 c58 c78
    rcases group103 with ⟨h104,h105,h106,h107,h108,h109,h110,h111,h112,h113⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h85) (And.intro (forced (a 2) 0 h81) (And.intro (forced (a 3) 0 h112) (And.intro (forced (a 4) 0 h89) (And.intro (forced (a 5) 0 h87) (And.intro (forced (a 6) 0 h90) (And.intro (forced (a 7) 0 h92) (And.intro (forced (a 8) 0 h99) (And.intro (forced (a 9) 0 h88) (And.intro (forced (a 10) 0 h100) (And.intro (forced (a 11) 0 h102) (And.intro (forced (a 12) 0 h91) (And.intro (forced (a 13) 0 h93) (And.intro (forced (a 14) 0 h95) (And.intro (forced (a 15) 0 h97) (And.intro (forced (a 16) 0 h108) (And.intro (forced (a 17) 0 h113) (And.intro (forced (a 18) 0 h109) (And.intro (forced (a 19) 0 h110) (And.intro (forced (a 20) 0 h60) (And.intro (forced (a 21) 0 h94) (And.intro (forced (a 22) 0 h96) (And.intro (forced (a 23) 0 h98) (And.intro (forced (a 24) 0 h101) (And.intro (forced (a 25) 0 h72) (And.intro (forced (a 26) 0 h104) (And.intro (forced (a 27) 0 h66) (And.intro (forced (a 28) 0 h105) (And.intro (forced (a 29) 0 h106) (And.intro (forced (a 30) 0 h107) (forced (a 31) 0 h111))))))))))))))))))))))))))))))))
  · have h114 : a 1 ∈ [1] := List.mem_singleton.mpr q84
    have group115 := chunk17 a h8 h114 h9 h82 h79 h45 h80 h21 h22 h40 h26 h51 h67 h29 h38 h61 h39 c6 c7 c16 c17 c18 c20 c21 c22 c24 c25 c26 c27 c28 c29 c31 c32
    rcases group115 with ⟨h116,h117,h118,h119,h120,h121,h122,h123,h124,h125,h126,h127,h128,h129,h130,h131⟩
    have group132 := chunk18 a h73 h129 h76 h120 h78 h122 h77 h124 h4 h130 h59 h62 h127 h75 h5 h131 h10 c14 c37 c42 c44 c46 c48 c51 c57 c58 c78
    rcases group132 with ⟨h133,h134,h135,h136,h137,h138,h139,h140,h141,h142⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h114) (And.intro (forced (a 2) 0 h81) (And.intro (forced (a 3) 2 h141) (And.intro (forced (a 4) 1 h118) (And.intro (forced (a 5) 3 h116) (And.intro (forced (a 6) 1 h119) (And.intro (forced (a 7) 1 h121) (And.intro (forced (a 8) 2 h128) (And.intro (forced (a 9) 2 h117) (And.intro (forced (a 10) 1 h129) (And.intro (forced (a 11) 4 h131) (And.intro (forced (a 12) 2 h120) (And.intro (forced (a 13) 2 h122) (And.intro (forced (a 14) 2 h124) (And.intro (forced (a 15) 1 h126) (And.intro (forced (a 16) 3 h137) (And.intro (forced (a 17) 3 h142) (And.intro (forced (a 18) 3 h138) (And.intro (forced (a 19) 3 h139) (And.intro (forced (a 20) 0 h60) (And.intro (forced (a 21) 1 h123) (And.intro (forced (a 22) 1 h125) (And.intro (forced (a 23) 1 h127) (And.intro (forced (a 24) 6 h130) (And.intro (forced (a 25) 0 h72) (And.intro (forced (a 26) 12 h133) (And.intro (forced (a 27) 0 h66) (And.intro (forced (a 28) 2 h134) (And.intro (forced (a 29) 1 h135) (And.intro (forced (a 30) 6 h136) (forced (a 31) 1 h140))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_196
