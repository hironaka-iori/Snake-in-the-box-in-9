import PartitionData205_189
import PartitionPiece205_189_0
import PartitionPiece205_189_1
import PartitionPiece205_189_2
import PartitionPiece205_189_3
import PartitionPiece205_189_4
namespace PartitionCover205_189
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0])
    (start6 : a 6 ∈ [0,1,2,3,4,5])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0,1,2,3,4,5])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start12 : a 12 ∈ [0,1,2,3,4,5])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8])
    (start18 : a 18 ∈ [0,1,2])
    (start19 : a 19 ∈ [0,1,2])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start22 : a 22 ∈ [0])
    (start23 : a 23 ∈ [0,1,2])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start29 : a 29 ∈ [0,1,2,3,4,5])
    (start30 : a 30 ∈ [0,1,2,3,4,5])
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
    (c19 : edge r19 (a 5) (a 7)=true)
    (c20 : edge r20 (a 5) (a 13)=true)
    (c21 : edge r21 (a 5) (a 20)=true)
    (c22 : edge r22 (a 6) (a 7)=true)
    (c23 : edge r23 (a 6) (a 14)=true)
    (c24 : edge r24 (a 6) (a 21)=true)
    (c25 : edge r25 (a 7) (a 15)=true)
    (c26 : edge r26 (a 7) (a 22)=true)
    (c27 : edge r27 (a 8) (a 9)=true)
    (c28 : edge r28 (a 8) (a 10)=true)
    (c29 : edge r29 (a 8) (a 12)=true)
    (c30 : edge r30 (a 8) (a 23)=true)
    (c31 : edge r31 (a 9) (a 11)=true)
    (c32 : edge r32 (a 9) (a 13)=true)
    (c33 : edge r33 (a 9) (a 24)=true)
    (c34 : edge r34 (a 10) (a 11)=true)
    (c35 : edge r35 (a 10) (a 14)=true)
    (c36 : edge r36 (a 10) (a 25)=true)
    (c37 : edge r37 (a 11) (a 15)=true)
    (c38 : edge r38 (a 11) (a 26)=true)
    (c39 : edge r39 (a 12) (a 13)=true)
    (c40 : edge r40 (a 12) (a 14)=true)
    (c41 : edge r41 (a 12) (a 27)=true)
    (c42 : edge r42 (a 13) (a 15)=true)
    (c43 : edge r43 (a 13) (a 28)=true)
    (c44 : edge r44 (a 14) (a 15)=true)
    (c45 : edge r45 (a 14) (a 29)=true)
    (c46 : edge r46 (a 15) (a 30)=true)
    (c47 : edge r47 (a 16) (a 17)=true)
    (c48 : edge r48 (a 16) (a 18)=true)
    (c49 : edge r49 (a 16) (a 23)=true)
    (c50 : edge r50 (a 17) (a 19)=true)
    (c51 : edge r51 (a 17) (a 20)=true)
    (c52 : edge r52 (a 17) (a 24)=true)
    (c53 : edge r53 (a 18) (a 19)=true)
    (c54 : edge r54 (a 18) (a 21)=true)
    (c55 : edge r55 (a 18) (a 25)=true)
    (c56 : edge r56 (a 19) (a 22)=true)
    (c57 : edge r57 (a 19) (a 26)=true)
    (c58 : edge r58 (a 20) (a 22)=true)
    (c59 : edge r59 (a 20) (a 28)=true)
    (c60 : edge r60 (a 21) (a 22)=true)
    (c61 : edge r61 (a 21) (a 29)=true)
    (c62 : edge r62 (a 22) (a 30)=true)
    (c63 : edge r63 (a 23) (a 24)=true)
    (c64 : edge r64 (a 23) (a 25)=true)
    (c65 : edge r65 (a 23) (a 27)=true)
    (c66 : edge r66 (a 24) (a 26)=true)
    (c67 : edge r67 (a 24) (a 28)=true)
    (c68 : edge r68 (a 25) (a 26)=true)
    (c69 : edge r69 (a 25) (a 29)=true)
    (c70 : edge r70 (a 26) (a 30)=true)
    (c71 : edge r71 (a 27) (a 28)=true)
    (c72 : edge r72 (a 27) (a 29)=true)
    (c73 : edge r73 (a 28) (a 30)=true)
    (c74 : edge r74 (a 29) (a 30)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0) ∨
      (a 0=0 ∧ a 1=0 ∧ a 2=1 ∧ a 3=1 ∧ a 4=1 ∧ a 5=0 ∧ a 6=3 ∧ a 7=1 ∧ a 8=2 ∧ a 9=2 ∧ a 10=18 ∧ a 11=19 ∧ a 12=2 ∧ a 13=3 ∧ a 14=18 ∧ a 15=1 ∧ a 16=6 ∧ a 17=3 ∧ a 18=0 ∧ a 19=0 ∧ a 20=3 ∧ a 21=1 ∧ a 22=0 ∧ a 23=0 ∧ a 24=6 ∧ a 25=4 ∧ a 26=4 ∧ a 27=2 ∧ a 28=6 ∧ a 29=2 ∧ a 30=2) := by
  have group1 := chunk0 a start8 start0 start16 c3 c4
  rcases group1 with ⟨h2,h3⟩
  have group4 := chunk1 a start9 start1 start17 start10 start2 c7 c8 c11
  rcases group4 with ⟨h5,h6,h7⟩
  have group8 := chunk2 a h7 start2 start18 c11 c12
  rcases group8 with ⟨h9,h10⟩
  have group11 := chunk3 a h10 start2 start11 start3 c12 c14
  rcases group11 with ⟨h12,h13⟩
  have group14 := chunk4 a h13 start3 start4 start5 start6 start12 start13 start20 c14 c16 c17 c18 c20 c21
  rcases group14 with ⟨h15,h16,h17,h18,h19,h20⟩
  have group21 := chunk5 a h20 start5 h17 start7 start14 c21 c22 c23
  rcases group21 with ⟨h22,h23,h24⟩
  have group25 := chunk6 a h24 h23 start21 start15 start7 h2 h5 c23 c24 c25 c27
  rcases group25 with ⟨h26,h27,h28,h29⟩
  have group30 := chunk7 a h29 h5 h18 start24 h15 h9 h26 c27 c29 c33 c34 c35
  rcases group30 with ⟨h31,h32,h33,h34,h35⟩
  have group36 := chunk8 a h35 h26 start25 c35 c36
  rcases group36 with ⟨h37,h38,h39⟩
  have group40 := chunk9 a h39 h37 h28 h34 start26 start27 h32 c36 c37 c38 c41
  rcases group40 with ⟨h41,h42,h43,h44⟩
  have group45 := chunk10 a h44 h32 h19 h42 start28 c41 c42 c43
  rcases group45 with ⟨h46,h47,h48,h49⟩
  have group50 := chunk11 a h49 h47 start29 h38 start30 h48 h3 h12 start23 h22 h6 start19 c43 c45 c46 c48 c49 c51 c53 c59
  rcases group50 with ⟨h51,h52,h53,h54,h55,h56,h57⟩
  have group58 := chunk12 a h51 h56 h27 start22 h53 h33 h55 h41 h43 h52 c59 c60 c62 c63 c67 c68 c69
  rcases group58 with ⟨h59,h60,h61,h62,h63,h64⟩
  have group65 := chunk13 a h64 h63 h47 h59 c43 c69
  rcases group65 with ⟨h66,h67⟩
  rcases (show a 2=0 ∨ a 2=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start2) with q68 | q69
  · have h70 : a 2 ∈ [0] := List.mem_singleton.mpr q68
    have group71 := chunk14 a start3 h70 h23 h37 start7 h34 h16 h32 h38 h60 h31 h5 h67 h62 h63 h48 h43 c9 c10 c11 c13 c14 c17 c18 c23 c24 c28 c31 c32 c33 c36 c37 c38
    rcases group71 with ⟨h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87⟩
    have group88 := chunk15 a h46 h78 h59 h83 h66 h79 h56 h61 h87 h6 h54 c41 c43 c45 c47 c51 c59 c70
    rcases group88 with ⟨h89,h90,h91,h92,h93,h94,h95⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h70) (And.intro (forced (a 3) 0 h72) (And.intro (forced (a 4) 0 h77) (And.intro (forced (a 5) 0 start5) (And.intro (forced (a 6) 0 h73) (And.intro (forced (a 7) 0 h75) (And.intro (forced (a 8) 0 h81) (And.intro (forced (a 9) 0 h82) (And.intro (forced (a 10) 0 h74) (And.intro (forced (a 11) 0 h76) (And.intro (forced (a 12) 0 h78) (And.intro (forced (a 13) 0 h83) (And.intro (forced (a 14) 0 h79) (And.intro (forced (a 15) 0 h86) (And.intro (forced (a 16) 0 h95) (And.intro (forced (a 17) 0 h94) (And.intro (forced (a 18) 0 h12) (And.intro (forced (a 19) 0 h57) (And.intro (forced (a 20) 0 h92) (And.intro (forced (a 21) 0 h80) (And.intro (forced (a 22) 0 start22) (And.intro (forced (a 23) 0 h55) (And.intro (forced (a 24) 0 h84) (And.intro (forced (a 25) 0 h85) (And.intro (forced (a 26) 0 h87) (And.intro (forced (a 27) 0 h89) (And.intro (forced (a 28) 0 h90) (And.intro (forced (a 29) 0 h91) (forced (a 30) 0 h93)))))))))))))))))))))))))))))))
  · have h96 : a 2 ∈ [1] := List.mem_singleton.mpr q69
    have group97 := chunk16 a start3 h96 h23 h37 start7 h34 h16 h32 h38 h60 h31 h5 h67 h62 h63 h48 h43 c9 c10 c11 c13 c14 c17 c18 c23 c24 c28 c31 c32 c33 c36 c37 c38
    rcases group97 with ⟨h98,h99,h100,h101,h102,h103,h104,h105,h106,h107,h108,h109,h110,h111,h112,h113⟩
    have group114 := chunk17 a h46 h104 h59 h109 h66 h105 h56 h61 h113 h6 h54 c41 c43 c45 c47 c51 c59 c70
    rcases group114 with ⟨h115,h116,h117,h118,h119,h120,h121⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 1 h96) (And.intro (forced (a 3) 1 h98) (And.intro (forced (a 4) 1 h103) (And.intro (forced (a 5) 0 start5) (And.intro (forced (a 6) 3 h99) (And.intro (forced (a 7) 1 h101) (And.intro (forced (a 8) 2 h107) (And.intro (forced (a 9) 2 h108) (And.intro (forced (a 10) 18 h100) (And.intro (forced (a 11) 19 h102) (And.intro (forced (a 12) 2 h104) (And.intro (forced (a 13) 3 h109) (And.intro (forced (a 14) 18 h105) (And.intro (forced (a 15) 1 h112) (And.intro (forced (a 16) 6 h121) (And.intro (forced (a 17) 3 h120) (And.intro (forced (a 18) 0 h12) (And.intro (forced (a 19) 0 h57) (And.intro (forced (a 20) 3 h118) (And.intro (forced (a 21) 1 h106) (And.intro (forced (a 22) 0 start22) (And.intro (forced (a 23) 0 h55) (And.intro (forced (a 24) 6 h110) (And.intro (forced (a 25) 4 h111) (And.intro (forced (a 26) 4 h113) (And.intro (forced (a 27) 2 h115) (And.intro (forced (a 28) 6 h116) (And.intro (forced (a 29) 2 h117) (forced (a 30) 2 h119)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_189
