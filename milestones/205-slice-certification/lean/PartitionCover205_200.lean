import PartitionData205_200
import PartitionPiece205_200_0
import PartitionPiece205_200_1
import PartitionPiece205_200_2
import PartitionPiece205_200_3
import PartitionPiece205_200_4
import PartitionPiece205_200_5
namespace PartitionCover205_200
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1,2])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0,1,2,3,4,5])
    (start7 : a 7 ∈ [0,1,2])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (start16 : a 16 ∈ [0,1,2,3,4,5])
    (start17 : a 17 ∈ [0,1,2,3,4,5])
    (start18 : a 18 ∈ [0,1,2,3,4,5])
    (start19 : a 19 ∈ [0,1,2])
    (start20 : a 20 ∈ [0,1,2,3,4,5])
    (start21 : a 21 ∈ [0,1,2])
    (start22 : a 22 ∈ [0,1,2,3,4,5])
    (start23 : a 23 ∈ [0,1,2,3,4,5])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=4 ∧ a 3=2 ∧ a 4=8 ∧ a 5=4 ∧ a 6=4 ∧ a 7=2 ∧ a 8=8 ∧ a 9=4 ∧ a 10=1 ∧ a 11=12 ∧ a 12=1 ∧ a 13=1 ∧ a 14=12 ∧ a 15=6 ∧ a 16=2 ∧ a 17=2 ∧ a 18=4 ∧ a 19=0 ∧ a 20=2 ∧ a 21=2 ∧ a 22=1 ∧ a 23=1 ∧ a 24=4 ∧ a 25=1 ∧ a 26=19 ∧ a 27=9 ∧ a 28=3 ∧ a 29=2 ∧ a 30=19 ∧ a 31=9) := by
  have group1 := chunk0 a start2 start0 start4 start8 c1 c2 c3
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 start0 start16 start3 h2 start6 start10 c3 c4 c9 c10 c11
  rcases group5 with ⟨h6,h7,h8,h9,h10⟩
  have group11 := chunk2 a start18 h2 start11 h8 c12 c14
  rcases group11 with ⟨h12,h13⟩
  have group14 := chunk3 a h3 h9 start12 c17 c18
  rcases group14 with ⟨h15,h16⟩
  have group17 := chunk4 a h16 h15 start20 start7 h9 start14 c18 c19 c23 c24
  rcases group17 with ⟨h18,h19,h20,h21⟩
  have group22 := chunk5 a h21 h9 start22 start15 h20 start9 h6 h18 c24 c25 c26 c28 c30
  rcases group22 with ⟨h23,h24,h25,h26,h27,h28⟩
  have group29 := chunk6 a h28 h27 start24 h26 h13 c30 c31 c32
  rcases group29 with ⟨h30,h31,h32⟩
  have group33 := chunk7 a h32 h13 start13 c32 c33
  rcases group33 with ⟨h34,h35,h36⟩
  have group37 := chunk8 a h36 h34 start25 h10 h35 start26 c33 c34 c35 c37
  rcases group37 with ⟨h38,h39,h40,h41⟩
  have group42 := chunk9 a h41 h40 h25 h35 start27 c37 c38 c39
  rcases group42 with ⟨h43,h44,h45⟩
  have group46 := chunk10 a h45 h35 h30 h38 h23 start28 start29 c39 c40 c41 c42 c44
  rcases group46 with ⟨h47,h48,h49,h50,h51⟩
  have group52 := chunk11 a h51 h38 start30 h49 c44 c46
  rcases group52 with ⟨h53,h54⟩
  have group55 := chunk12 a h54 h49 start31 h44 c46 c47
  rcases group55 with ⟨h56,h57⟩
  have group58 := chunk13 a h57 h44 start17 h7 h31 h39 start19 h12 h43 c47 c48 c51 c54 c55 c57
  rcases group58 with ⟨h59,h60,h61,h62,h63⟩
  have group64 := chunk14 a h63 h12 start23 h62 start21 h24 c57 c58 c63 c65
  rcases group64 with ⟨h65,h66,h67,h68⟩
  have group69 := chunk15 a h68 h66 h56 h59 h65 h47 c65 c66 c67 c73 c74
  rcases group69 with ⟨h70,h71,h72,h73,h74⟩
  have group75 := chunk16 a h50 h71 start1 h34 start5 h15 h48 h38 h27 h40 h73 h49 c7 c16 c18 c21 c28 c37 c46 c77
  rcases group75 with ⟨h76,h77,h78,h79,h80,h81,h82⟩
  have group83 := chunk17 a h7 h60 h19 h67 h79 h78 c16 c48 c60
  rcases group83 with ⟨h84,h85,h86⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h77) with q87 | q88
  · have h89 : a 1 ∈ [0] := List.mem_singleton.mpr q87
    have group90 := chunk18 a h8 h89 h78 h34 h60 h2 h9 h81 h12 h20 h86 h48 h85 h67 h82 h70 h44 c5 c6 c7 c8 c9 c10 c11 c12 c13 c16 c18 c19 c22 c24 c25 c26
    rcases group90 with ⟨h91,h92,h93,h94,h95,h96,h97,h98,h99,h100,h101,h102,h103,h104,h105,h106⟩
    have group107 := chunk19 a h80 h93 h61 h73 h97 h35 h106 h74 h38 h53 h71 h104 h72 h84 h94 h66 h103 h39 h76 c28 c31 c37 c38 c39 c43 c44 c46 c47 c48 c63 c68 c70
    rcases group107 with ⟨h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119,h120⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h89) (And.intro (forced (a 2) 0 h95) (And.intro (forced (a 3) 0 h91) (And.intro (forced (a 4) 0 h100) (And.intro (forced (a 5) 0 h92) (And.intro (forced (a 6) 0 h96) (And.intro (forced (a 7) 0 h99) (And.intro (forced (a 8) 0 h108) (And.intro (forced (a 9) 0 h93) (And.intro (forced (a 10) 0 h97) (And.intro (forced (a 11) 0 h111) (And.intro (forced (a 12) 0 h101) (And.intro (forced (a 13) 0 h113) (And.intro (forced (a 14) 0 h104) (And.intro (forced (a 15) 0 h106) (And.intro (forced (a 16) 0 h117) (And.intro (forced (a 17) 0 h94) (And.intro (forced (a 18) 0 h98) (And.intro (forced (a 19) 0 h62) (And.intro (forced (a 20) 0 h102) (And.intro (forced (a 21) 0 h103) (And.intro (forced (a 22) 0 h105) (And.intro (forced (a 23) 0 h118) (And.intro (forced (a 24) 0 h109) (And.intro (forced (a 25) 0 h119) (And.intro (forced (a 26) 0 h110) (And.intro (forced (a 27) 0 h112) (And.intro (forced (a 28) 0 h120) (And.intro (forced (a 29) 0 h114) (And.intro (forced (a 30) 0 h115) (forced (a 31) 0 h116))))))))))))))))))))))))))))))))
  · have h121 : a 1 ∈ [1] := List.mem_singleton.mpr q88
    have group122 := chunk20 a h8 h121 h78 h34 h60 h2 h9 h81 h12 h20 h86 h48 h85 h67 h82 h70 h44 c5 c6 c7 c8 c9 c10 c11 c12 c13 c16 c18 c19 c22 c24 c25 c26
    rcases group122 with ⟨h123,h124,h125,h126,h127,h128,h129,h130,h131,h132,h133,h134,h135,h136,h137,h138⟩
    have group139 := chunk21 a h80 h125 h61 h73 h129 h35 h138 h74 h38 h53 h71 h136 h72 h84 h126 h66 h135 h39 h76 c28 c31 c37 c38 c39 c43 c44 c46 c47 c48 c63 c68 c70
    rcases group139 with ⟨h140,h141,h142,h143,h144,h145,h146,h147,h148,h149,h150,h151,h152⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h121) (And.intro (forced (a 2) 4 h127) (And.intro (forced (a 3) 2 h123) (And.intro (forced (a 4) 8 h132) (And.intro (forced (a 5) 4 h124) (And.intro (forced (a 6) 4 h128) (And.intro (forced (a 7) 2 h131) (And.intro (forced (a 8) 8 h140) (And.intro (forced (a 9) 4 h125) (And.intro (forced (a 10) 1 h129) (And.intro (forced (a 11) 12 h143) (And.intro (forced (a 12) 1 h133) (And.intro (forced (a 13) 1 h145) (And.intro (forced (a 14) 12 h136) (And.intro (forced (a 15) 6 h138) (And.intro (forced (a 16) 2 h149) (And.intro (forced (a 17) 2 h126) (And.intro (forced (a 18) 4 h130) (And.intro (forced (a 19) 0 h62) (And.intro (forced (a 20) 2 h134) (And.intro (forced (a 21) 2 h135) (And.intro (forced (a 22) 1 h137) (And.intro (forced (a 23) 1 h150) (And.intro (forced (a 24) 4 h141) (And.intro (forced (a 25) 1 h151) (And.intro (forced (a 26) 19 h142) (And.intro (forced (a 27) 9 h144) (And.intro (forced (a 28) 3 h152) (And.intro (forced (a 29) 2 h146) (And.intro (forced (a 30) 19 h147) (forced (a 31) 9 h148))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_200
