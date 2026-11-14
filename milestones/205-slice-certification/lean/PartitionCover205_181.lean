import PartitionData205_181
import PartitionPiece205_181_0
import PartitionPiece205_181_1
import PartitionPiece205_181_2
import PartitionPiece205_181_3
import PartitionPiece205_181_4
namespace PartitionCover205_181
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8])
    (start6 : a 6 ∈ [0,1,2,3,4,5])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start13 : a 13 ∈ [0,1,2,3,4,5])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0,1])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0,1])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start26 : a 26 ∈ [0,1,2,3,4,5])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start28 : a 28 ∈ [0,1,2])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=0 ∧ a 3=1 ∧ a 4=1 ∧ a 5=2 ∧ a 6=1 ∧ a 7=3 ∧ a 8=6 ∧ a 9=3 ∧ a 10=1 ∧ a 11=6 ∧ a 12=2 ∧ a 13=0 ∧ a 14=4 ∧ a 15=12 ∧ a 16=1 ∧ a 17=1 ∧ a 18=1 ∧ a 19=1 ∧ a 20=2 ∧ a 21=0 ∧ a 22=0 ∧ a 23=6 ∧ a 24=6 ∧ a 25=0 ∧ a 26=3 ∧ a 27=0 ∧ a 28=1 ∧ a 29=2 ∧ a 30=6 ∧ a 31=2) := by
  have group1 := chunk0 a start4 start0 start8 start2 start18 c2 c3 c12
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a start7 start3 start11 start5 h2 c13 c14 c16
  rcases group5 with ⟨h6,h7,h8⟩
  have group9 := chunk2 a h8 h2 start6 start12 start20 c16 c17 c18 c19
  rcases group9 with ⟨h10,h11,h12,h13⟩
  have group14 := chunk3 a h13 h2 start13 h10 start21 start14 h11 c19 c21 c22 c24
  rcases group14 with ⟨h15,h16,h17,h18⟩
  have group19 := chunk4 a h18 h11 start22 start15 h6 c24 c25 c26
  rcases group19 with ⟨h20,h21,h22⟩
  have group23 := chunk5 a h22 h6 start23 c26 c27
  rcases group23 with ⟨h24,h25⟩
  have group26 := chunk6 a h25 h6 start9 h3 start10 h12 start24 c27 c28 c29 c30 c31
  rcases group26 with ⟨h27,h28,h29,h30,h31⟩
  have group32 := chunk7 a h31 h3 start25 h28 h7 h29 start26 h24 c31 c34 c35 c37 c38
  rcases group32 with ⟨h33,h34,h35,h36,h37⟩
  have group38 := chunk8 a h37 h35 start27 h16 h30 c38 c39 c40 c43
  rcases group38 with ⟨h39,h40,h41⟩
  have group42 := chunk9 a h39 h41 start29 c43 c44
  rcases group42 with ⟨h43,h44⟩
  have group45 := chunk10 a h44 h41 start30 h20 c44 c46
  rcases group45 with ⟨h46,h47⟩
  have group48 := chunk11 a h47 h20 start31 h43 h17 start17 h34 c46 c47 c53 c54
  rcases group48 with ⟨h49,h50,h51,h52⟩
  have group53 := chunk12 a h52 start17 h15 h21 h51 h46 h27 h49 h50 c54 c61 c64 c65 c66 c67
  rcases group53 with ⟨h54,h55,h56,h57,h58,h59,h60⟩
  have group61 := chunk13 a h60 h58 h54 h33 h36 h59 h40 start28 h46 h10 h41 c21 c67 c68 c69 c74 c75 c76
  rcases group61 with ⟨h62,h63,h64,h65,h66,h67⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q68 | q69
  · have h70 : a 1 ∈ [0] := List.mem_singleton.mpr q68
    have group71 := chunk14 a h28 h70 start17 h3 h29 h30 h33 h35 h20 h64 h43 h65 h62 start16 start18 start19 h58 c7 c8 c28 c29 c30 c31 c32 c36 c37 c38 c46 c47 c48 c49 c52 c58
    rcases group71 with ⟨h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87⟩
    have group88 := chunk15 a h66 h82 h46 h83 start3 h78 h2 h76 h55 h11 h79 h6 h81 h67 c14 c16 c18 c19 c24 c26 c77 c78
    rcases group88 with ⟨h89,h90,h91,h92,h93,h94,h95,h96⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h70) (And.intro (forced (a 2) 0 h4) (And.intro (forced (a 3) 0 h91) (And.intro (forced (a 4) 0 h92) (And.intro (forced (a 5) 0 h96) (And.intro (forced (a 6) 0 h94) (And.intro (forced (a 7) 0 h95) (And.intro (forced (a 8) 0 h74) (And.intro (forced (a 9) 0 h72) (And.intro (forced (a 10) 0 h75) (And.intro (forced (a 11) 0 h78) (And.intro (forced (a 12) 0 h76) (And.intro (forced (a 13) 0 h41) (And.intro (forced (a 14) 0 h79) (And.intro (forced (a 15) 0 h81) (And.intro (forced (a 16) 0 h84) (And.intro (forced (a 17) 0 h73) (And.intro (forced (a 18) 0 h85) (And.intro (forced (a 19) 0 h86) (And.intro (forced (a 20) 0 h93) (And.intro (forced (a 21) 0 h57) (And.intro (forced (a 22) 0 h56) (And.intro (forced (a 23) 0 h87) (And.intro (forced (a 24) 0 h77) (And.intro (forced (a 25) 0 h63) (And.intro (forced (a 26) 0 h80) (And.intro (forced (a 27) 0 h40) (And.intro (forced (a 28) 0 h89) (And.intro (forced (a 29) 0 h90) (And.intro (forced (a 30) 0 h82) (forced (a 31) 0 h83))))))))))))))))))))))))))))))))
  · have h97 : a 1 ∈ [1] := List.mem_singleton.mpr q69
    have group98 := chunk16 a h28 h97 start17 h3 h29 h30 h33 h35 h20 h64 h43 h65 h62 start16 start18 start19 h58 c7 c8 c28 c29 c30 c31 c32 c36 c37 c38 c46 c47 c48 c49 c52 c58
    rcases group98 with ⟨h99,h100,h101,h102,h103,h104,h105,h106,h107,h108,h109,h110,h111,h112,h113,h114⟩
    have group115 := chunk17 a h66 h109 h46 h110 start3 h105 h2 h103 h55 h11 h106 h6 h108 h67 c14 c16 c18 c19 c24 c26 c77 c78
    rcases group115 with ⟨h116,h117,h118,h119,h120,h121,h122,h123⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h97) (And.intro (forced (a 2) 0 h4) (And.intro (forced (a 3) 1 h118) (And.intro (forced (a 4) 1 h119) (And.intro (forced (a 5) 2 h123) (And.intro (forced (a 6) 1 h121) (And.intro (forced (a 7) 3 h122) (And.intro (forced (a 8) 6 h101) (And.intro (forced (a 9) 3 h99) (And.intro (forced (a 10) 1 h102) (And.intro (forced (a 11) 6 h105) (And.intro (forced (a 12) 2 h103) (And.intro (forced (a 13) 0 h41) (And.intro (forced (a 14) 4 h106) (And.intro (forced (a 15) 12 h108) (And.intro (forced (a 16) 1 h111) (And.intro (forced (a 17) 1 h100) (And.intro (forced (a 18) 1 h112) (And.intro (forced (a 19) 1 h113) (And.intro (forced (a 20) 2 h120) (And.intro (forced (a 21) 0 h57) (And.intro (forced (a 22) 0 h56) (And.intro (forced (a 23) 6 h114) (And.intro (forced (a 24) 6 h104) (And.intro (forced (a 25) 0 h63) (And.intro (forced (a 26) 3 h107) (And.intro (forced (a 27) 0 h40) (And.intro (forced (a 28) 1 h116) (And.intro (forced (a 29) 2 h117) (And.intro (forced (a 30) 6 h109) (forced (a 31) 2 h110))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_181
