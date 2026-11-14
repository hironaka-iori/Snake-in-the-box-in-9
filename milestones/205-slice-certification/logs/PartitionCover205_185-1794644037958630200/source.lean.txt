import PartitionData205_185
import PartitionPiece205_185_0
import PartitionPiece205_185_1
import PartitionPiece205_185_2
import PartitionPiece205_185_3
import PartitionPiece205_185_4
import PartitionPiece205_185_5
import PartitionPiece205_185_6
namespace PartitionCover205_185
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2])
    (start2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0,1,2,3])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start20 : a 20 ∈ [0,1,2,3])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6])
    (start25 : a 25 ∈ [0,1,2,3])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=6 ∧ a 3=6 ∧ a 4=3 ∧ a 5=12 ∧ a 6=9 ∧ a 7=10 ∧ a 8=2 ∧ a 9=4 ∧ a 10=23 ∧ a 11=18 ∧ a 12=9 ∧ a 13=2 ∧ a 14=4 ∧ a 15=2 ∧ a 16=1 ∧ a 17=2 ∧ a 18=3 ∧ a 19=6 ∧ a 20=2 ∧ a 21=4 ∧ a 22=1 ∧ a 23=1 ∧ a 24=4 ∧ a 25=2 ∧ a 26=10 ∧ a 27=9 ∧ a 28=14 ∧ a 29=4 ∧ a 30=4 ∧ a 31=6) := by
  have group1 := chunk0 a start2 start0 start5 start1 c1 c6
  rcases group1 with ⟨h2,h3⟩
  have group4 := chunk1 a start9 start1 start17 start3 h2 start6 c7 c8 c9 c10
  rcases group4 with ⟨h5,h6,h7,h8,h9⟩
  have group10 := chunk2 a h9 h2 start10 c10 c11
  rcases group10 with ⟨h11,h12⟩
  have group13 := chunk3 a h12 h2 start18 start7 h8 start11 c11 c12 c13 c14
  rcases group13 with ⟨h14,h15,h16,h17⟩
  have group18 := chunk4 a h17 h8 start19 start12 start4 start13 h3 h5 start8 c14 c15 c18 c21 c28
  rcases group18 with ⟨h19,h20,h21,h22,h23⟩
  have group24 := chunk5 a h23 start8 h14 h21 c28 c29 c30
  rcases group24 with ⟨h25,h26,h27,h28⟩
  have group29 := chunk6 a h28 h26 start24 c30 c31
  rcases group29 with ⟨h30,h31⟩
  have group32 := chunk7 a h31 h26 h19 h25 h22 c31 c32 c33
  rcases group32 with ⟨h33,h34,h35⟩
  have group36 := chunk8 a h35 h25 start25 h34 h27 c33 c34 c35
  rcases group36 with ⟨h37,h38,h39⟩
  have group40 := chunk9 a h39 h27 start14 start26 c35 c36 c37
  rcases group40 with ⟨h41,h42,h43⟩
  have group44 := chunk10 a h43 h27 start15 h41 start27 c37 c38 c39
  rcases group44 with ⟨h45,h46,h47⟩
  have group48 := chunk11 a h47 h41 h30 h37 start28 start29 h46 h42 start30 c39 c40 c42 c44 c45 c46
  rcases group48 with ⟨h49,h50,h51,h52,h53,h54⟩
  have group55 := chunk12 a h54 h42 start31 h53 h15 start16 start21 h7 c46 c47 c49 c53
  rcases group55 with ⟨h56,h57,h58,h59⟩
  have group60 := chunk13 a h59 h7 h20 h58 start22 c53 c55 c56
  rcases group60 with ⟨h61,h62,h63⟩
  have group64 := chunk14 a h63 h58 h45 start23 h62 h49 start20 h61 c56 c57 c58 c59 c60 c61
  rcases group64 with ⟨h65,h66,h67,h68,h69⟩
  have group70 := chunk15 a h65 h69 h51 h67 h61 h52 c61 c62 c63 c64 c65
  rcases group70 with ⟨h71,h72,h73,h74⟩
  have group75 := chunk16 a h73 h71 h57 h72 h33 h56 h66 h8 h6 c5 c65 c67 c70 c74
  rcases group75 with ⟨h76,h77,h78,h79,h80⟩
  have group81 := chunk17 a h80 h6 h3 h2 h11 h58 h16 c5 c6 c9 c10 c12 c13
  rcases group81 with ⟨h82,h83,h84,h85,h86⟩
  have group87 := chunk18 a h86 h82 h41 h83 h37 h61 h85 c13 c14 c21 c22 c23
  rcases group87 with ⟨h88,h89,h90,h91⟩
  have group92 := chunk19 a h91 h88 h42 h76 h41 h53 h37 h74 start4 h90 c16 c23 c24 c27 c38 c44
  rcases group92 with ⟨h93,h94,h95,h96,h97⟩
  have group98 := chunk20 a h97 h90 c16
  have h99 := group98
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h6) with q100 | q101
  · have h102 : a 1 ∈ [0] := List.mem_singleton.mpr q100
    have group103 := chunk21 a h89 h102 h25 h84 h58 h94 h95 h62 h93 h42 h71 h26 h50 h96 h38 h27 h66 c5 c7 c9 c12 c13 c14 c15 c23 c24 c25 c28 c30 c33 c34 c36 c37
    rcases group103 with ⟨h104,h105,h106,h107,h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119⟩
    have group120 := chunk22 a h53 h109 h68 h78 h115 h79 h112 h77 start16 h107 h69 h33 h7 h117 h61 h76 h113 h74 h99 h90 c16 c18 c38 c39 c42 c46 c47 c49 c50 c51 c54 c60 c65 c72
    rcases group120 with ⟨h121,h122,h123,h124,h125,h126,h127,h128,h129,h130,h131,h132,h133,h134⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h102) (And.intro (forced (a 2) 0 h106) (And.intro (forced (a 3) 0 h104) (And.intro (forced (a 4) 0 h133) (And.intro (forced (a 5) 0 h134) (And.intro (forced (a 6) 0 h111) (And.intro (forced (a 7) 0 h108) (And.intro (forced (a 8) 0 h114) (And.intro (forced (a 9) 0 h105) (And.intro (forced (a 10) 0 h118) (And.intro (forced (a 11) 0 h109) (And.intro (forced (a 12) 0 h115) (And.intro (forced (a 13) 0 h116) (And.intro (forced (a 14) 0 h112) (And.intro (forced (a 15) 0 h121) (And.intro (forced (a 16) 0 h126) (And.intro (forced (a 17) 0 h129) (And.intro (forced (a 18) 0 h107) (And.intro (forced (a 19) 0 h110) (And.intro (forced (a 20) 0 h127) (And.intro (forced (a 21) 0 h130) (And.intro (forced (a 22) 0 h113) (And.intro (forced (a 23) 0 h131) (And.intro (forced (a 24) 0 h128) (And.intro (forced (a 25) 0 h117) (And.intro (forced (a 26) 0 h119) (And.intro (forced (a 27) 0 h122) (And.intro (forced (a 28) 0 h123) (And.intro (forced (a 29) 0 h132) (And.intro (forced (a 30) 0 h124) (forced (a 31) 0 h125))))))))))))))))))))))))))))))))
  · have h135 : a 1 ∈ [1] := List.mem_singleton.mpr q101
    have group136 := chunk23 a h89 h135 h25 h84 h58 h94 h95 h62 h93 h42 h71 h26 h50 h96 h38 h27 h66 c5 c7 c9 c12 c13 c14 c15 c23 c24 c25 c28 c30 c33 c34 c36 c37
    rcases group136 with ⟨h137,h138,h139,h140,h141,h142,h143,h144,h145,h146,h147,h148,h149,h150,h151,h152⟩
    have group153 := chunk24 a h53 h142 h68 h78 h148 h79 h145 h77 start16 h140 h69 h33 h7 h150 h61 h76 h146 h74 h99 h90 c16 c18 c38 c39 c42 c46 c47 c49 c50 c51 c54 c60 c65 c72
    rcases group153 with ⟨h154,h155,h156,h157,h158,h159,h160,h161,h162,h163,h164,h165,h166,h167⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h135) (And.intro (forced (a 2) 6 h139) (And.intro (forced (a 3) 6 h137) (And.intro (forced (a 4) 3 h166) (And.intro (forced (a 5) 12 h167) (And.intro (forced (a 6) 9 h144) (And.intro (forced (a 7) 10 h141) (And.intro (forced (a 8) 2 h147) (And.intro (forced (a 9) 4 h138) (And.intro (forced (a 10) 23 h151) (And.intro (forced (a 11) 18 h142) (And.intro (forced (a 12) 9 h148) (And.intro (forced (a 13) 2 h149) (And.intro (forced (a 14) 4 h145) (And.intro (forced (a 15) 2 h154) (And.intro (forced (a 16) 1 h159) (And.intro (forced (a 17) 2 h162) (And.intro (forced (a 18) 3 h140) (And.intro (forced (a 19) 6 h143) (And.intro (forced (a 20) 2 h160) (And.intro (forced (a 21) 4 h163) (And.intro (forced (a 22) 1 h146) (And.intro (forced (a 23) 1 h164) (And.intro (forced (a 24) 4 h161) (And.intro (forced (a 25) 2 h150) (And.intro (forced (a 26) 10 h152) (And.intro (forced (a 27) 9 h155) (And.intro (forced (a 28) 14 h156) (And.intro (forced (a 29) 4 h165) (And.intro (forced (a 30) 4 h157) (forced (a 31) 6 h158))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_185
