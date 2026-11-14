import PartitionData205_192
import PartitionPiece205_192_0
import PartitionPiece205_192_1
import PartitionPiece205_192_2
import PartitionPiece205_192_3
import PartitionPiece205_192_4
namespace PartitionCover205_192
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3])
    (start3 : a 3 ∈ [0,1,2,3])
    (start4 : a 4 ∈ [0,1,2])
    (start5 : a 5 ∈ [0,1,2])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start12 : a 12 ∈ [0,1,2,3,4,5])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start16 : a 16 ∈ [0,1,2,3,4,5])
    (start17 : a 17 ∈ [0,1,2,3,4,5])
    (start18 : a 18 ∈ [0,1,2,3,4,5])
    (start19 : a 19 ∈ [0,1,2])
    (start20 : a 20 ∈ [0,1,2])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2])
    (start23 : a 23 ∈ [0,1,2,3,4,5])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8])
    (start28 : a 28 ∈ [0,1,2])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=2 ∧ a 3=2 ∧ a 4=0 ∧ a 5=1 ∧ a 6=6 ∧ a 7=3 ∧ a 8=2 ∧ a 9=4 ∧ a 10=4 ∧ a 11=0 ∧ a 12=1 ∧ a 13=4 ∧ a 14=4 ∧ a 15=6 ∧ a 16=1 ∧ a 17=1 ∧ a 18=1 ∧ a 19=0 ∧ a 20=0 ∧ a 21=1 ∧ a 22=0 ∧ a 23=1 ∧ a 24=0 ∧ a 25=8 ∧ a 26=6 ∧ a 27=3 ∧ a 28=1 ∧ a 29=8 ∧ a 30=6 ∧ a 31=6) := by
  have group1 := chunk0 a start2 start0 start8 start16 start9 start1 c1 c3 c4 c7
  rcases group1 with ⟨h2,h3,h4,h5⟩
  have group6 := chunk1 a h5 start1 start17 start3 h2 start6 start10 c7 c8 c9 c10 c11
  rcases group6 with ⟨h7,h8,h9,h10,h11⟩
  have group12 := chunk2 a h11 h2 start18 start11 h9 start19 c11 c12 c14 c15
  rcases group12 with ⟨h13,h14,h15,h16⟩
  have group17 := chunk3 a start5 start4 start7 start13 start21 h10 start22 start15 c16 c20 c21 c22 c25 c26
  rcases group17 with ⟨h18,h19,h20,h21,h22,h23⟩
  have group24 := chunk4 a h23 h19 h7 h3 h13 start12 c26 c28 c29 c30
  rcases group24 with ⟨h25,h26,h27,h28⟩
  have group29 := chunk5 a h28 h3 start24 h15 h26 h20 h27 c30 c31 c32 c33 c35
  rcases group29 with ⟨h30,h31,h32,h33,h34⟩
  have group35 := chunk6 a h34 h32 start14 c35 c36
  rcases group35 with ⟨h36,h37⟩
  have group38 := chunk7 a h37 h36 h25 h32 start27 start28 h30 start29 h33 c36 c38 c39 c42 c44
  rcases group38 with ⟨h39,h40,h41,h42,h43⟩
  have group44 := chunk8 a h43 h33 c44
  have h45 := group44
  have group46 := chunk9 a h45 h33 start30 h39 c44 c46
  rcases group46 with ⟨h47,h48⟩
  have group49 := chunk10 a start31 h40 h14 h4 start20 h21 h8 start22 start23 h16 h47 c47 c49 c50 c53 c56 c58 c64
  rcases group49 with ⟨h50,h51,h52,h53,h54,h55,h56⟩
  have group57 := chunk11 a h56 h53 h50 h55 start25 h31 c64 c67 c68
  rcases group57 with ⟨h58,h59,h60⟩
  have group61 := chunk12 a h60 h31 start26 c68 c69
  rcases group61 with ⟨h62,h63⟩
  have group64 := chunk13 a h63 h31 h62 h58 h59 h41 start4 h30 h22 h39 c18 c24 c69 c72 c75 c78
  rcases group64 with ⟨h65,h66,h67,h68,h69⟩
  have group70 := chunk14 a h19 h40 h31 h66 h65 h48 c26 c68 c69 c74
  rcases group70 with ⟨h71,h72,h73,h74⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q75 | q76
  · have h77 : a 1 ∈ [0] := List.mem_singleton.mpr q75
    have group78 := chunk15 a h9 h77 h2 h69 h36 h51 h71 h18 h33 h53 h39 h40 h55 h3 h30 h26 h42 c5 c9 c10 c11 c12 c13 c20 c21 c22 c24 c26 c27 c29 c30 c33 c42
    rcases group78 with ⟨h79,h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91,h92,h93,h94⟩
    have group95 := chunk16 a h58 h86 h74 h88 h4 h83 h8 h87 h66 h73 h67 h41 c44 c46 c49 c53 c71 c72 c74 c79
    rcases group95 with ⟨h96,h97,h98,h99,h100,h101,h102,h103⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h77) (And.intro (forced (a 2) 0 h80) (And.intro (forced (a 3) 0 h79) (And.intro (forced (a 4) 0 h68) (And.intro (forced (a 5) 0 h85) (And.intro (forced (a 6) 0 h81) (And.intro (forced (a 7) 0 h84) (And.intro (forced (a 8) 0 h91) (And.intro (forced (a 9) 0 h93) (And.intro (forced (a 10) 0 h82) (And.intro (forced (a 11) 0 h32) (And.intro (forced (a 12) 0 h92) (And.intro (forced (a 13) 0 h86) (And.intro (forced (a 14) 0 h88) (And.intro (forced (a 15) 0 h89) (And.intro (forced (a 16) 0 h98) (And.intro (forced (a 17) 0 h99) (And.intro (forced (a 18) 0 h83) (And.intro (forced (a 19) 0 h16) (And.intro (forced (a 20) 0 h52) (And.intro (forced (a 21) 0 h87) (And.intro (forced (a 22) 0 h54) (And.intro (forced (a 23) 0 h90) (And.intro (forced (a 24) 0 h72) (And.intro (forced (a 25) 0 h100) (And.intro (forced (a 26) 0 h101) (And.intro (forced (a 27) 0 h103) (And.intro (forced (a 28) 0 h94) (And.intro (forced (a 29) 0 h96) (And.intro (forced (a 30) 0 h97) (forced (a 31) 0 h102))))))))))))))))))))))))))))))))
  · have h104 : a 1 ∈ [1] := List.mem_singleton.mpr q76
    have group105 := chunk17 a h9 h104 h2 h69 h36 h51 h71 h18 h33 h53 h39 h40 h55 h3 h30 h26 h42 c5 c9 c10 c11 c12 c13 c20 c21 c22 c24 c26 c27 c29 c30 c33 c42
    rcases group105 with ⟨h106,h107,h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119,h120,h121⟩
    have group122 := chunk18 a h58 h113 h74 h115 h4 h110 h8 h114 h66 h73 h67 h41 c44 c46 c49 c53 c71 c72 c74 c79
    rcases group122 with ⟨h123,h124,h125,h126,h127,h128,h129,h130⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h104) (And.intro (forced (a 2) 2 h107) (And.intro (forced (a 3) 2 h106) (And.intro (forced (a 4) 0 h68) (And.intro (forced (a 5) 1 h112) (And.intro (forced (a 6) 6 h108) (And.intro (forced (a 7) 3 h111) (And.intro (forced (a 8) 2 h118) (And.intro (forced (a 9) 4 h120) (And.intro (forced (a 10) 4 h109) (And.intro (forced (a 11) 0 h32) (And.intro (forced (a 12) 1 h119) (And.intro (forced (a 13) 4 h113) (And.intro (forced (a 14) 4 h115) (And.intro (forced (a 15) 6 h116) (And.intro (forced (a 16) 1 h125) (And.intro (forced (a 17) 1 h126) (And.intro (forced (a 18) 1 h110) (And.intro (forced (a 19) 0 h16) (And.intro (forced (a 20) 0 h52) (And.intro (forced (a 21) 1 h114) (And.intro (forced (a 22) 0 h54) (And.intro (forced (a 23) 1 h117) (And.intro (forced (a 24) 0 h72) (And.intro (forced (a 25) 8 h127) (And.intro (forced (a 26) 6 h128) (And.intro (forced (a 27) 3 h130) (And.intro (forced (a 28) 1 h121) (And.intro (forced (a 29) 8 h123) (And.intro (forced (a 30) 6 h124) (forced (a 31) 6 h129))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_192
