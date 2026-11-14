import PartitionData205_191
import PartitionPiece205_191_0
import PartitionPiece205_191_1
import PartitionPiece205_191_2
import PartitionPiece205_191_3
import PartitionPiece205_191_4
import PartitionPiece205_191_5
import PartitionPiece205_191_6
namespace PartitionCover205_191
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2])
    (start2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start7 : a 7 ∈ [0,1,2,3])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8])
    (start20 : a 20 ∈ [0,1,2,3])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start28 : a 28 ∈ [0,1,2,3])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
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
      (a 0=0 ∧ a 1=2 ∧ a 2=9 ∧ a 3=9 ∧ a 4=1 ∧ a 5=4 ∧ a 6=9 ∧ a 7=0 ∧ a 8=3 ∧ a 9=5 ∧ a 10=5 ∧ a 11=4 ∧ a 12=20 ∧ a 13=6 ∧ a 14=9 ∧ a 15=21 ∧ a 16=5 ∧ a 17=3 ∧ a 18=13 ∧ a 19=6 ∧ a 20=3 ∧ a 21=4 ∧ a 22=3 ∧ a 23=12 ∧ a 24=16 ∧ a 25=18 ∧ a 26=12 ∧ a 27=3 ∧ a 28=0 ∧ a 29=18 ∧ a 30=5 ∧ a 31=18) := by
  have group1 := chunk0 a start2 start0 start16 start1 start5 start9 c1 c4 c6 c7
  rcases group1 with ⟨h2,h3,h4,h5,h6⟩
  have group7 := chunk1 a h6 h4 start17 start3 h2 start6 start10 c7 c8 c9 c10 c11
  rcases group7 with ⟨h8,h9,h10,h11,h12⟩
  have group13 := chunk2 a h12 h2 start18 start11 h10 c11 c12 c14
  rcases group13 with ⟨h14,h15,h16⟩
  have group17 := chunk3 a h16 h10 h11 start4 start12 c14 c17 c18
  rcases group17 with ⟨h18,h19,h20⟩
  have group21 := chunk4 a h20 start4 start13 h5 start21 c18 c21 c22
  rcases group21 with ⟨h22,h23,h24⟩
  have group25 := chunk5 a h24 h5 start7 h19 start14 start22 c22 c23 c24 c25
  rcases group25 with ⟨h26,h27,h28,h29⟩
  have group30 := chunk6 a h29 h19 start15 h27 start23 h14 start8 c25 c26 c27 c29
  rcases group30 with ⟨h31,h32,h33,h34⟩
  have group35 := chunk7 a h34 start8 start24 c29 c31
  rcases group35 with ⟨h36,h37⟩
  have group38 := chunk8 a h37 start8 h8 h18 c31 c32
  rcases group38 with ⟨h39,h40,h41⟩
  have group42 := chunk9 a h41 h40 start25 c32 c34
  rcases group42 with ⟨h43,h44⟩
  have group45 := chunk10 a h36 h43 start26 c35 c37
  rcases group45 with ⟨h46,h47⟩
  have group48 := chunk11 a h47 h46 h32 h43 c37 c38
  rcases group48 with ⟨h49,h50⟩
  have group51 := chunk12 a h50 h43 start27 c38 c39
  rcases group51 with ⟨h52,h53⟩
  have group54 := chunk13 a h53 h43 h22 h23 start28 start29 c39 c40 c42 c44
  rcases group54 with ⟨h55,h56,h57,h58,h59⟩
  have group60 := chunk14 a h59 h57 c44
  have h61 := group60
  have group62 := chunk15 a h61 h57 h52 h28 start30 c44 c45 c46
  rcases group62 with ⟨h63,h64,h65⟩
  have group66 := chunk16 a h65 h28 start31 h64 c46 c47
  rcases group66 with ⟨h67,h68⟩
  have group69 := chunk17 a h68 h64 h9 h3 start20 c47 c48 c50
  rcases group69 with ⟨h70,h71,h72⟩
  have group73 := chunk18 a h72 start20 h39 h71 h26 h15 h31 h49 c50 c51 c53 c56 c57
  rcases group73 with ⟨h74,h75,h76,h77,h78⟩
  have group79 := chunk19 a h78 h49 h33 h26 c57 c63
  rcases group79 with ⟨h80,h81⟩
  have group82 := chunk20 a h81 h26 h44 h76 h49 h55 c63 c68 c73
  rcases group82 with ⟨h83,h84,h85,h86⟩
  have group87 := chunk21 a h86 h85 h67 h63 h70 h2 h19 h10 h43 c10 c14 c73 c74 c78
  rcases group87 with ⟨h88,h89,h90,h91,h92,h93⟩
  have group94 := chunk22 a h93 h43 start19 h27 h64 start8 h40 h74 h77 h80 c14 c15 c26 c28 c48 c55
  rcases group94 with ⟨h95,h96,h97,h98,h99,h100,h101⟩
  have group102 := chunk23 a h96 h101 h84 h90 c55 c72
  rcases group102 with ⟨h103,h104⟩
  rcases (show a 1=0 ∨ a 1=2 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h4) with q105 | q106
  · have h107 : a 1 ∈ [0] := List.mem_singleton.mpr q105
    have group108 := chunk24 a h95 h107 h5 h92 h19 h46 h43 h103 start4 h56 h75 h57 h26 h28 h31 h98 h76 c5 c6 c9 c10 c11 c14 c15 c16 c18 c19 c21 c22 c24 c25 c29 c31
    rcases group108 with ⟨h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119,h120,h121,h122,h123,h124⟩
    have group125 := chunk25 a h85 h113 h64 h114 h90 h119 h89 h121 h91 h99 h118 h101 h115 h83 h104 h124 h88 h40 h123 h100 c28 c37 c38 c44 c46 c47 c48 c50 c55 c58 c68 c73
    rcases group125 with ⟨h126,h127,h128,h129,h130,h131,h132,h133,h134,h135,h136,h137⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h107) (And.intro (forced (a 2) 0 h111) (And.intro (forced (a 3) 0 h109) (And.intro (forced (a 4) 0 h116) (And.intro (forced (a 5) 0 h110) (And.intro (forced (a 6) 0 h112) (And.intro (forced (a 7) 0 h97) (And.intro (forced (a 8) 0 h123) (And.intro (forced (a 9) 0 h136) (And.intro (forced (a 10) 0 h113) (And.intro (forced (a 11) 0 h114) (And.intro (forced (a 12) 0 h117) (And.intro (forced (a 13) 0 h119) (And.intro (forced (a 14) 0 h121) (And.intro (forced (a 15) 0 h127) (And.intro (forced (a 16) 0 h131) (And.intro (forced (a 17) 0 h137) (And.intro (forced (a 18) 0 h132) (And.intro (forced (a 19) 0 h115) (And.intro (forced (a 20) 0 h118) (And.intro (forced (a 21) 0 h120) (And.intro (forced (a 22) 0 h122) (And.intro (forced (a 23) 0 h133) (And.intro (forced (a 24) 0 h124) (And.intro (forced (a 25) 0 h134) (And.intro (forced (a 26) 0 h126) (And.intro (forced (a 27) 0 h135) (And.intro (forced (a 28) 0 h58) (And.intro (forced (a 29) 0 h128) (And.intro (forced (a 30) 0 h129) (forced (a 31) 0 h130))))))))))))))))))))))))))))))))
  · have h138 : a 1 ∈ [2] := List.mem_singleton.mpr q106
    have group139 := chunk26 a h95 h138 h5 h92 h19 h46 h43 h103 start4 h56 h75 h57 h26 h28 h31 h98 h76 c5 c6 c9 c10 c11 c14 c15 c16 c18 c19 c21 c22 c24 c25 c29 c31
    rcases group139 with ⟨h140,h141,h142,h143,h144,h145,h146,h147,h148,h149,h150,h151,h152,h153,h154,h155⟩
    have group156 := chunk27 a h85 h144 h64 h145 h90 h150 h89 h152 h91 h99 h149 h101 h146 h83 h104 h155 h88 h40 h154 h100 c28 c37 c38 c44 c46 c47 c48 c50 c55 c58 c68 c73
    rcases group156 with ⟨h157,h158,h159,h160,h161,h162,h163,h164,h165,h166,h167,h168⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 2 h138) (And.intro (forced (a 2) 9 h142) (And.intro (forced (a 3) 9 h140) (And.intro (forced (a 4) 1 h147) (And.intro (forced (a 5) 4 h141) (And.intro (forced (a 6) 9 h143) (And.intro (forced (a 7) 0 h97) (And.intro (forced (a 8) 3 h154) (And.intro (forced (a 9) 5 h167) (And.intro (forced (a 10) 5 h144) (And.intro (forced (a 11) 4 h145) (And.intro (forced (a 12) 20 h148) (And.intro (forced (a 13) 6 h150) (And.intro (forced (a 14) 9 h152) (And.intro (forced (a 15) 21 h158) (And.intro (forced (a 16) 5 h162) (And.intro (forced (a 17) 3 h168) (And.intro (forced (a 18) 13 h163) (And.intro (forced (a 19) 6 h146) (And.intro (forced (a 20) 3 h149) (And.intro (forced (a 21) 4 h151) (And.intro (forced (a 22) 3 h153) (And.intro (forced (a 23) 12 h164) (And.intro (forced (a 24) 16 h155) (And.intro (forced (a 25) 18 h165) (And.intro (forced (a 26) 12 h157) (And.intro (forced (a 27) 3 h166) (And.intro (forced (a 28) 0 h58) (And.intro (forced (a 29) 18 h159) (And.intro (forced (a 30) 5 h160) (forced (a 31) 18 h161))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_191
