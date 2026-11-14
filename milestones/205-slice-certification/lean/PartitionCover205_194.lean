import PartitionData205_194
import PartitionPiece205_194_0
import PartitionPiece205_194_1
import PartitionPiece205_194_2
import PartitionPiece205_194_3
import PartitionPiece205_194_4
namespace PartitionCover205_194
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2,3])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1,2,3])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7])
    (start6 : a 6 ∈ [0,1,2,3,4,5])
    (start7 : a 7 ∈ [0,1,2])
    (start8 : a 8 ∈ [0,1,2,3,4,5])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7])
    (start10 : a 10 ∈ [0,1,2,3,4,5])
    (start11 : a 11 ∈ [0,1,2])
    (start12 : a 12 ∈ [0,1,2])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (start14 : a 14 ∈ [0,1,2,3,4,5])
    (start15 : a 15 ∈ [0,1,2])
    (start16 : a 16 ∈ [0,1,2,3])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start20 : a 20 ∈ [0,1,2,3])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8])
    (start31 : a 31 ∈ [0,1,2,3,4,5,6,7,8])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=1 ∧ a 3=1 ∧ a 4=1 ∧ a 5=4 ∧ a 6=1 ∧ a 7=1 ∧ a 8=1 ∧ a 9=4 ∧ a 10=1 ∧ a 11=0 ∧ a 12=0 ∧ a 13=4 ∧ a 14=1 ∧ a 15=1 ∧ a 16=2 ∧ a 17=4 ∧ a 18=0 ∧ a 19=0 ∧ a 20=2 ∧ a 21=4 ∧ a 22=3 ∧ a 23=6 ∧ a 24=0 ∧ a 25=6 ∧ a 26=1 ∧ a 27=3 ∧ a 28=6 ∧ a 29=6 ∧ a 30=3 ∧ a 31=3) := by
  have group1 := chunk0 a start8 start0 start16 start5 start1 start9 start17 start2 start3 start6 c3 c4 c6 c7 c8 c9 c10
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8⟩
  have group9 := chunk1 a start18 h7 start3 start11 start19 c12 c14 c15
  rcases group9 with ⟨h10,h11,h12,h13⟩
  have group14 := chunk2 a h13 h11 h4 start4 h8 start13 start21 start14 start22 c15 c16 c17 c21 c22 c24 c25
  rcases group14 with ⟨h15,h16,h17,h18,h19,h20,h21⟩
  have group22 := chunk3 a h21 h17 h5 h2 start10 start12 start24 c25 c28 c29 c30 c31
  rcases group22 with ⟨h23,h24,h25,h26,h27⟩
  have group28 := chunk4 a h27 h2 h18 h24 h20 h25 start15 h12 start27 c31 c33 c36 c38 c39
  rcases group28 with ⟨h29,h30,h31,h32,h33⟩
  have group34 := chunk5 a h33 h12 start28 h26 start29 h30 c39 c42 c44
  rcases group34 with ⟨h35,h36,h37⟩
  have group38 := chunk6 a h37 h30 start30 h31 start31 h32 h6 h3 h10 c44 c46 c47 c48 c49
  rcases group38 with ⟨h39,h40,h41,h42,h43⟩
  have group44 := chunk7 a h43 h3 start20 h15 h42 h19 h23 start26 c49 c50 c52 c53 c56 c57
  rcases group44 with ⟨h45,h46,h47,h48,h49,h50⟩
  have group51 := chunk8 a h50 h45 c57
  have h52 := group51
  have group53 := chunk9 a start23 h47 h48 c58 c63
  have h54 := group53
  have group55 := chunk10 a h40 h49 h41 h54 start25 h29 c66 c67 c68
  rcases group55 with ⟨h56,h57,h58⟩
  have group59 := chunk11 a h58 h29 h52 h36 h39 c68 c69 c70 c72
  rcases group59 with ⟨h60,h61,h62,h63,h64⟩
  have group65 := chunk12 a h64 h60 h56 h62 start1 h11 h7 start7 h16 h30 c5 c9 c13 c21 c72 c74
  rcases group65 with ⟨h66,h67,h68,h69,h70,h71⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h68) with q72 | q73
  · have h74 : a 1 ∈ [0] := List.mem_singleton.mpr q72
    have group75 := chunk13 a h11 h74 h69 h17 h70 start4 h46 h31 h49 h32 h54 h25 h67 h57 h3 h63 h62 c5 c9 c10 c13 c17 c19 c24 c25 c26 c27 c36 c46 c47 c50 c62 c74
    rcases group75 with ⟨h76,h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91⟩
    have group92 := chunk14 a h35 h88 h66 h90 h2 h86 h42 h89 h48 h60 h71 h24 h30 c22 c28 c29 c33 c48 c53 c71 c75 c76
    rcases group92 with ⟨h93,h94,h95,h96,h97,h98,h99,h100,h101⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h74) (And.intro (forced (a 2) 0 h77) (And.intro (forced (a 3) 0 h76) (And.intro (forced (a 4) 0 h80) (And.intro (forced (a 5) 0 h99) (And.intro (forced (a 6) 0 h78) (And.intro (forced (a 7) 0 h79) (And.intro (forced (a 8) 0 h95) (And.intro (forced (a 9) 0 h100) (And.intro (forced (a 10) 0 h86) (And.intro (forced (a 11) 0 h12) (And.intro (forced (a 12) 0 h26) (And.intro (forced (a 13) 0 h101) (And.intro (forced (a 14) 0 h82) (And.intro (forced (a 15) 0 h84) (And.intro (forced (a 16) 0 h89) (And.intro (forced (a 17) 0 h96) (And.intro (forced (a 18) 0 h45) (And.intro (forced (a 19) 0 h47) (And.intro (forced (a 20) 0 h81) (And.intro (forced (a 21) 0 h97) (And.intro (forced (a 22) 0 h83) (And.intro (forced (a 23) 0 h85) (And.intro (forced (a 24) 0 h61) (And.intro (forced (a 25) 0 h98) (And.intro (forced (a 26) 0 h91) (And.intro (forced (a 27) 0 h93) (And.intro (forced (a 28) 0 h90) (And.intro (forced (a 29) 0 h94) (And.intro (forced (a 30) 0 h87) (forced (a 31) 0 h88))))))))))))))))))))))))))))))))
  · have h102 : a 1 ∈ [1] := List.mem_singleton.mpr q73
    have group103 := chunk15 a h11 h102 h69 h17 h70 start4 h46 h31 h49 h32 h54 h25 h67 h57 h3 h63 h62 c5 c9 c10 c13 c17 c19 c24 c25 c26 c27 c36 c46 c47 c50 c62 c74
    rcases group103 with ⟨h104,h105,h106,h107,h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119⟩
    have group120 := chunk16 a h35 h116 h66 h118 h2 h114 h42 h117 h48 h60 h71 h24 h30 c22 c28 c29 c33 c48 c53 c71 c75 c76
    rcases group120 with ⟨h121,h122,h123,h124,h125,h126,h127,h128,h129⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h102) (And.intro (forced (a 2) 1 h105) (And.intro (forced (a 3) 1 h104) (And.intro (forced (a 4) 1 h108) (And.intro (forced (a 5) 4 h127) (And.intro (forced (a 6) 1 h106) (And.intro (forced (a 7) 1 h107) (And.intro (forced (a 8) 1 h123) (And.intro (forced (a 9) 4 h128) (And.intro (forced (a 10) 1 h114) (And.intro (forced (a 11) 0 h12) (And.intro (forced (a 12) 0 h26) (And.intro (forced (a 13) 4 h129) (And.intro (forced (a 14) 1 h110) (And.intro (forced (a 15) 1 h112) (And.intro (forced (a 16) 2 h117) (And.intro (forced (a 17) 4 h124) (And.intro (forced (a 18) 0 h45) (And.intro (forced (a 19) 0 h47) (And.intro (forced (a 20) 2 h109) (And.intro (forced (a 21) 4 h125) (And.intro (forced (a 22) 3 h111) (And.intro (forced (a 23) 6 h113) (And.intro (forced (a 24) 0 h61) (And.intro (forced (a 25) 6 h126) (And.intro (forced (a 26) 1 h119) (And.intro (forced (a 27) 3 h121) (And.intro (forced (a 28) 6 h118) (And.intro (forced (a 29) 6 h122) (And.intro (forced (a 30) 3 h115) (forced (a 31) 3 h116))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_194
