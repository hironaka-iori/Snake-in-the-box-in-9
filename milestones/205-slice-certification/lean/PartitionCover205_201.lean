import PartitionData205_201
import PartitionPiece205_201_0
import PartitionPiece205_201_1
import PartitionPiece205_201_2
import PartitionPiece205_201_3
import PartitionPiece205_201_4
import PartitionPiece205_201_5
import PartitionPiece205_201_6
namespace PartitionCover205_201
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2])
    (start2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start3 : a 3 ∈ [0,1,2])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0,1,2,3,4,5])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=8 ∧ a 3=2 ∧ a 4=1 ∧ a 5=2 ∧ a 6=5 ∧ a 7=4 ∧ a 8=8 ∧ a 9=2 ∧ a 10=1 ∧ a 11=16 ∧ a 12=8 ∧ a 13=4 ∧ a 14=13 ∧ a 15=8 ∧ a 16=12 ∧ a 17=6 ∧ a 18=8 ∧ a 19=1 ∧ a 20=12 ∧ a 21=6 ∧ a 22=11 ∧ a 23=1 ∧ a 24=6 ∧ a 25=3 ∧ a 26=20 ∧ a 27=11 ∧ a 28=4 ∧ a 29=8 ∧ a 30=23 ∧ a 31=11) := by
  have group1 := chunk0 a start2 start0 start8 c1 c3
  rcases group1 with ⟨h2,h3⟩
  have group4 := chunk1 a h3 start0 start16 c3 c4
  rcases group4 with ⟨h5,h6⟩
  have group7 := chunk2 a h6 start0 start5 start1 c4 c6
  rcases group7 with ⟨h8,h9⟩
  have group10 := chunk3 a start17 start1 start3 h2 start6 start10 c8 c9 c10 c11
  rcases group10 with ⟨h11,h12,h13,h14⟩
  have group15 := chunk4 a h14 h2 start18 c11 c12
  rcases group15 with ⟨h16,h17⟩
  have group18 := chunk5 a h17 h2 start7 h12 start11 c12 c13 c14
  rcases group18 with ⟨h19,h20,h21⟩
  have group22 := chunk6 a h21 h12 start19 start12 start4 start20 c14 c15 c18 c19
  rcases group22 with ⟨h23,h24,h25,h26⟩
  have group27 := chunk7 a h26 start4 start13 h9 start21 h20 h13 c19 c21 c22 c23
  rcases group27 with ⟨h28,h29,h30,h31⟩
  have group32 := chunk8 a h31 h13 start14 start22 c23 c24 c25
  rcases group32 with ⟨h33,h34,h35⟩
  have group36 := chunk9 a h35 h13 start15 h33 start23 start9 h5 h25 c25 c26 c27 c28 c30
  rcases group36 with ⟨h37,h38,h39,h40,h41⟩
  have group42 := chunk10 a h41 h5 start24 c30 c31
  rcases group42 with ⟨h43,h44⟩
  have group45 := chunk11 a h44 h5 h23 h40 h29 start25 c31 c32 c33 c34
  rcases group45 with ⟨h46,h47,h48,h49⟩
  have group50 := chunk12 a h49 h40 h16 h47 h34 start26 c34 c35 c36 c37
  rcases group50 with ⟨h51,h52,h53,h54,h55⟩
  have group56 := chunk13 a h55 h52 h38 h53 start27 c37 c38 c39
  rcases group56 with ⟨h57,h58,h59⟩
  have group60 := chunk14 a h43 h48 start28 start29 c40 c42 c44
  rcases group60 with ⟨h61,h62,h63⟩
  have group64 := chunk15 a h63 h48 start30 h54 c44 c46
  rcases group64 with ⟨h65,h66⟩
  have group67 := chunk16 a h66 h54 start31 h58 h11 h8 h24 c46 c47 c48 c52
  rcases group67 with ⟨h68,h69,h70,h71⟩
  have group72 := chunk17 a h71 h70 h51 h19 h37 c52 c54 c55 c56
  rcases group72 with ⟨h73,h74,h75,h76⟩
  have group77 := chunk18 a h76 h19 h57 h39 h73 h59 h30 h28 h62 c56 c57 c58 c59 c60 c62
  rcases group77 with ⟨h78,h79,h80,h81,h82,h83⟩
  have group84 := chunk19 a h83 h62 h82 h80 h65 h78 h68 h69 c62 c63 c64 c65 c66 c67
  rcases group84 with ⟨h85,h86,h87,h88,h89,h90⟩
  have group91 := chunk20 a h46 h75 h79 h81 h90 h62 h89 start1 h40 h9 h33 h54 h8 h74 c7 c20 c46 c48 c68 c73 c75 c77
  rcases group91 with ⟨h92,h93,h94,h95,h96,h97,h98,h99,h100⟩
  have group101 := chunk21 a h100 h74 h85 h86 start4 h98 c16 c48 c60
  rcases group101 with ⟨h102,h103,h104⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h97) with q105 | q106
  · have h107 : a 1 ∈ [0] := List.mem_singleton.mpr q105
    have group108 := chunk22 a h12 h107 h40 h74 h2 h13 h52 h19 h33 h73 h104 h61 h103 h99 h88 h58 h5 c5 c7 c8 c9 c10 c11 c12 c13 c15 c17 c18 c19 c24 c25 c26 c28
    rcases group108 with ⟨h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119,h120,h121,h122,h123,h124⟩
    have group125 := chunk23 a h92 h124 h48 h110 h75 h93 h114 h53 h123 h81 h95 h119 h87 h96 h121 h94 h102 h111 h86 h80 h98 h118 c16 c31 c33 c34 c37 c38 c39 c42 c44 c46 c47 c48 c53 c63
    rcases group125 with ⟨h126,h127,h128,h129,h130,h131,h132,h133,h134,h135,h136,h137,h138,h139⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h107) (And.intro (forced (a 2) 0 h112) (And.intro (forced (a 3) 0 h109) (And.intro (forced (a 4) 0 h118) (And.intro (forced (a 5) 0 h139) (And.intro (forced (a 6) 0 h113) (And.intro (forced (a 7) 0 h116) (And.intro (forced (a 8) 0 h124) (And.intro (forced (a 9) 0 h110) (And.intro (forced (a 10) 0 h114) (And.intro (forced (a 11) 0 h130) (And.intro (forced (a 12) 0 h119) (And.intro (forced (a 13) 0 h127) (And.intro (forced (a 14) 0 h121) (And.intro (forced (a 15) 0 h123) (And.intro (forced (a 16) 0 h136) (And.intro (forced (a 17) 0 h111) (And.intro (forced (a 18) 0 h115) (And.intro (forced (a 19) 0 h117) (And.intro (forced (a 20) 0 h120) (And.intro (forced (a 21) 0 h137) (And.intro (forced (a 22) 0 h122) (And.intro (forced (a 23) 0 h138) (And.intro (forced (a 24) 0 h126) (And.intro (forced (a 25) 0 h128) (And.intro (forced (a 26) 0 h129) (And.intro (forced (a 27) 0 h131) (And.intro (forced (a 28) 0 h132) (And.intro (forced (a 29) 0 h133) (And.intro (forced (a 30) 0 h134) (forced (a 31) 0 h135))))))))))))))))))))))))))))))))
  · have h140 : a 1 ∈ [1] := List.mem_singleton.mpr q106
    have group141 := chunk24 a h12 h140 h40 h74 h2 h13 h52 h19 h33 h73 h104 h61 h103 h99 h88 h58 h5 c5 c7 c8 c9 c10 c11 c12 c13 c15 c17 c18 c19 c24 c25 c26 c28
    rcases group141 with ⟨h142,h143,h144,h145,h146,h147,h148,h149,h150,h151,h152,h153,h154,h155,h156,h157⟩
    have group158 := chunk25 a h92 h157 h48 h143 h75 h93 h147 h53 h156 h81 h95 h152 h87 h96 h154 h94 h102 h144 h86 h80 h98 h151 c16 c31 c33 c34 c37 c38 c39 c42 c44 c46 c47 c48 c53 c63
    rcases group158 with ⟨h159,h160,h161,h162,h163,h164,h165,h166,h167,h168,h169,h170,h171,h172⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h140) (And.intro (forced (a 2) 8 h145) (And.intro (forced (a 3) 2 h142) (And.intro (forced (a 4) 1 h151) (And.intro (forced (a 5) 2 h172) (And.intro (forced (a 6) 5 h146) (And.intro (forced (a 7) 4 h149) (And.intro (forced (a 8) 8 h157) (And.intro (forced (a 9) 2 h143) (And.intro (forced (a 10) 1 h147) (And.intro (forced (a 11) 16 h163) (And.intro (forced (a 12) 8 h152) (And.intro (forced (a 13) 4 h160) (And.intro (forced (a 14) 13 h154) (And.intro (forced (a 15) 8 h156) (And.intro (forced (a 16) 12 h169) (And.intro (forced (a 17) 6 h144) (And.intro (forced (a 18) 8 h148) (And.intro (forced (a 19) 1 h150) (And.intro (forced (a 20) 12 h153) (And.intro (forced (a 21) 6 h170) (And.intro (forced (a 22) 11 h155) (And.intro (forced (a 23) 1 h171) (And.intro (forced (a 24) 6 h159) (And.intro (forced (a 25) 3 h161) (And.intro (forced (a 26) 20 h162) (And.intro (forced (a 27) 11 h164) (And.intro (forced (a 28) 4 h165) (And.intro (forced (a 29) 8 h166) (And.intro (forced (a 30) 23 h167) (forced (a 31) 11 h168))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_201
