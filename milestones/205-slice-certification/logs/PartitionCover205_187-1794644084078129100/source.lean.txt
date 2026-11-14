import PartitionData205_187
import PartitionPiece205_187_0
import PartitionPiece205_187_1
import PartitionPiece205_187_2
import PartitionPiece205_187_3
import PartitionPiece205_187_4
import PartitionPiece205_187_5
import PartitionPiece205_187_6
namespace PartitionCover205_187
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1,2])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start12 : a 12 ∈ [0,1,2,3])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start16 : a 16 ∈ [0,1,2,3])
    (start17 : a 17 ∈ [0,1,2,3,4,5])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=8 ∧ a 3=6 ∧ a 4=9 ∧ a 5=20 ∧ a 6=8 ∧ a 7=3 ∧ a 8=1 ∧ a 9=2 ∧ a 10=2 ∧ a 11=6 ∧ a 12=2 ∧ a 13=4 ∧ a 14=2 ∧ a 15=1 ∧ a 16=1 ∧ a 17=3 ∧ a 18=12 ∧ a 19=6 ∧ a 20=9 ∧ a 21=18 ∧ a 22=11 ∧ a 23=9 ∧ a 24=9 ∧ a 25=10 ∧ a 26=5 ∧ a 27=8 ∧ a 28=4 ∧ a 29=10 ∧ a 30=2 ∧ a 31=5) := by
  have group1 := chunk0 a start2 start0 c1
  have h2 := group1
  have group3 := chunk1 a h2 start0 start4 start5 start1 c1 c2 c6
  rcases group3 with ⟨h4,h5,h6⟩
  have group7 := chunk2 a h6 start1 start9 start3 h4 c6 c7 c9
  rcases group7 with ⟨h8,h9,h10⟩
  have group11 := chunk3 a h10 h4 start6 c9 c10
  rcases group11 with ⟨h12,h13⟩
  have group14 := chunk4 a h13 h4 start10 c10 c11
  rcases group14 with ⟨h15,h16⟩
  have group17 := chunk5 a h16 h4 start18 c11 c12
  rcases group17 with ⟨h18,h19⟩
  have group20 := chunk6 a h19 h4 start11 h12 start19 c12 c14 c15
  rcases group20 with ⟨h21,h22,h23⟩
  have group24 := chunk7 a h23 h12 h8 h5 h15 start12 start20 start13 c15 c16 c17 c18 c19 c21
  rcases group24 with ⟨h25,h26,h27,h28,h29,h30⟩
  have group31 := chunk8 a h30 h26 start21 c21 c22
  rcases group31 with ⟨h32,h33⟩
  have group34 := chunk9 a h33 h26 start7 h15 start14 c22 c23 c24
  rcases group34 with ⟨h35,h36,h37⟩
  have group38 := chunk10 a h37 h15 start22 start15 h36 start23 c24 c25 c26 c27
  rcases group38 with ⟨h39,h40,h41,h42⟩
  have group43 := chunk11 a h42 h36 h18 start8 start24 h32 h9 c27 c29 c31 c33
  rcases group43 with ⟨h44,h45,h46,h47⟩
  have group48 := chunk12 a start25 h9 c34
  have h49 := group48
  have group50 := chunk13 a h49 h9 h22 h45 start26 h41 c34 c35 c37 c38
  rcases group50 with ⟨h51,h52,h53,h54⟩
  have group55 := chunk14 a start27 h52 start28 h28 h54 h47 start29 c39 c42 c43 c44
  rcases group55 with ⟨h56,h57,h58,h59⟩
  have group60 := chunk15 a h59 h47 c44
  have h61 := group60
  have group62 := chunk16 a h61 h47 start30 h39 start31 h58 c44 c46 c47
  rcases group62 with ⟨h63,h64,h65⟩
  have group66 := chunk17 a h65 h58 start16 start17 h29 h46 h35 c47 c48 c50 c51 c53
  rcases group66 with ⟨h67,h68,h69,h70,h71,h72⟩
  have group73 := chunk18 a h72 h69 h21 h25 h53 h44 h70 c53 c55 c57 c58 c60
  rcases group73 with ⟨h74,h75,h76,h77,h78,h79⟩
  have group80 := chunk19 a h57 h79 h63 h74 h78 h40 h51 h71 h56 h64 h77 h67 h12 h52 h26 h27 c14 c16 c62 c64 c65 c68 c71 c74 c75
  rcases group80 with ⟨h81,h82,h83,h84,h85,h86,h87,h88,h89⟩
  have group90 := chunk20 a h89 h27 c16
  have h91 := group90
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q92 | q93
  · have h94 : a 1 ∈ [0] := List.mem_singleton.mpr q92
    have group95 := chunk21 a h88 h94 h91 h9 h69 h36 h52 h76 h27 h15 h28 h79 h39 h40 start8 h45 h71 c5 c6 c7 c8 c13 c14 c15 c16 c17 c18 c19 c24 c25 c28 c29 c31
    rcases group95 with ⟨h96,h97,h98,h99,h100,h101,h102,h103,h104,h105,h106,h107,h108,h109,h110,h111⟩
    have group112 := chunk22 a h84 h98 h77 h110 h58 h101 h85 h47 h105 h81 h86 h107 h87 h68 h99 h75 h102 h83 h74 h106 h82 h4 h104 c10 c34 c37 c38 c39 c40 c42 c46 c47 c48 c55 c58 c60 c72
    rcases group112 with ⟨h113,h114,h115,h116,h117,h118,h119,h120,h121,h122,h123,h124,h125,h126⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h94) (And.intro (forced (a 2) 0 h126) (And.intro (forced (a 3) 0 h96) (And.intro (forced (a 4) 0 h103) (And.intro (forced (a 5) 0 h97) (And.intro (forced (a 6) 0 h104) (And.intro (forced (a 7) 0 h100) (And.intro (forced (a 8) 0 h109) (And.intro (forced (a 9) 0 h98) (And.intro (forced (a 10) 0 h110) (And.intro (forced (a 11) 0 h101) (And.intro (forced (a 12) 0 h105) (And.intro (forced (a 13) 0 h117) (And.intro (forced (a 14) 0 h107) (And.intro (forced (a 15) 0 h115) (And.intro (forced (a 16) 0 h121) (And.intro (forced (a 17) 0 h99) (And.intro (forced (a 18) 0 h122) (And.intro (forced (a 19) 0 h102) (And.intro (forced (a 20) 0 h106) (And.intro (forced (a 21) 0 h124) (And.intro (forced (a 22) 0 h108) (And.intro (forced (a 23) 0 h123) (And.intro (forced (a 24) 0 h111) (And.intro (forced (a 25) 0 h113) (And.intro (forced (a 26) 0 h114) (And.intro (forced (a 27) 0 h116) (And.intro (forced (a 28) 0 h118) (And.intro (forced (a 29) 0 h125) (And.intro (forced (a 30) 0 h119) (forced (a 31) 0 h120))))))))))))))))))))))))))))))))
  · have h127 : a 1 ∈ [1] := List.mem_singleton.mpr q93
    have group128 := chunk23 a h88 h127 h91 h9 h69 h36 h52 h76 h27 h15 h28 h79 h39 h40 start8 h45 h71 c5 c6 c7 c8 c13 c14 c15 c16 c17 c18 c19 c24 c25 c28 c29 c31
    rcases group128 with ⟨h129,h130,h131,h132,h133,h134,h135,h136,h137,h138,h139,h140,h141,h142,h143,h144⟩
    have group145 := chunk24 a h84 h131 h77 h143 h58 h134 h85 h47 h138 h81 h86 h140 h87 h68 h132 h75 h135 h83 h74 h139 h82 h4 h137 c10 c34 c37 c38 c39 c40 c42 c46 c47 c48 c55 c58 c60 c72
    rcases group145 with ⟨h146,h147,h148,h149,h150,h151,h152,h153,h154,h155,h156,h157,h158,h159⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h127) (And.intro (forced (a 2) 8 h159) (And.intro (forced (a 3) 6 h129) (And.intro (forced (a 4) 9 h136) (And.intro (forced (a 5) 20 h130) (And.intro (forced (a 6) 8 h137) (And.intro (forced (a 7) 3 h133) (And.intro (forced (a 8) 1 h142) (And.intro (forced (a 9) 2 h131) (And.intro (forced (a 10) 2 h143) (And.intro (forced (a 11) 6 h134) (And.intro (forced (a 12) 2 h138) (And.intro (forced (a 13) 4 h150) (And.intro (forced (a 14) 2 h140) (And.intro (forced (a 15) 1 h148) (And.intro (forced (a 16) 1 h154) (And.intro (forced (a 17) 3 h132) (And.intro (forced (a 18) 12 h155) (And.intro (forced (a 19) 6 h135) (And.intro (forced (a 20) 9 h139) (And.intro (forced (a 21) 18 h157) (And.intro (forced (a 22) 11 h141) (And.intro (forced (a 23) 9 h156) (And.intro (forced (a 24) 9 h144) (And.intro (forced (a 25) 10 h146) (And.intro (forced (a 26) 5 h147) (And.intro (forced (a 27) 8 h149) (And.intro (forced (a 28) 4 h151) (And.intro (forced (a 29) 10 h158) (And.intro (forced (a 30) 2 h152) (forced (a 31) 5 h153))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_187
