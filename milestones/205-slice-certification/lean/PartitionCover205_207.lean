import PartitionData205_207
import PartitionPiece205_207_0
import PartitionPiece205_207_1
import PartitionPiece205_207_2
import PartitionPiece205_207_3
namespace PartitionCover205_207
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1,2])
    (start6 : a 6 ∈ [0,1,2,3])
    (start7 : a 7 ∈ [0,1,2,3])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8])
    (start13 : a 13 ∈ [0,1,2,3,4,5])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start15 : a 15 ∈ [0,1,2,3,4,5])
    (start16 : a 16 ∈ [0,1,2,3,4,5])
    (start17 : a 17 ∈ [0,1,2,3,4,5])
    (start18 : a 18 ∈ [0,1,2])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start20 : a 20 ∈ [0,1,2,3,4,5])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start24 : a 24 ∈ [0,1,2,3,4,5])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start26 : a 26 ∈ [0,1,2,3,4,5])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start29 : a 29 ∈ [0,1,2,3,4,5])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=3 ∧ a 3=1 ∧ a 4=1 ∧ a 5=0 ∧ a 6=3 ∧ a 7=3 ∧ a 8=2 ∧ a 9=2 ∧ a 10=0 ∧ a 11=2 ∧ a 12=1 ∧ a 13=1 ∧ a 14=1 ∧ a 15=2 ∧ a 16=1 ∧ a 17=1 ∧ a 18=0 ∧ a 19=6 ∧ a 20=1 ∧ a 21=1 ∧ a 22=0 ∧ a 23=1 ∧ a 24=0 ∧ a 25=2 ∧ a 26=1 ∧ a 27=2 ∧ a 28=1 ∧ a 29=1 ∧ a 30=1 ∧ a 31=1) := by
  have group1 := chunk0 a start2 start0 start8 start16 start9 start1 c1 c3 c4 c7
  rcases group1 with ⟨h2,h3,h4,h5⟩
  have group6 := chunk1 a h5 start1 start6 h2 start10 start18 c7 c10 c11 c12
  rcases group6 with ⟨h7,h8,h9,h10⟩
  have group11 := chunk2 a h10 h2 start11 start3 start12 start4 start20 start7 start5 h8 start14 c12 c14 c18 c19 c20 c23 c24
  rcases group11 with ⟨h12,h13,h14,h15,h16,h17⟩
  have group18 := chunk3 a h17 h8 start15 h16 start23 c24 c26 c27
  rcases group18 with ⟨h19,h20,h21⟩
  have group22 := chunk4 a h21 h16 h7 h3 h14 start24 h13 c27 c28 c30 c31 c32
  rcases group22 with ⟨h23,h24,h25,h26,h27⟩
  have group28 := chunk5 a h27 h24 start13 h19 h9 start26 c32 c33 c36 c37
  rcases group28 with ⟨h29,h30,h31,h32⟩
  have group33 := chunk6 a h32 h9 start28 h25 start29 h30 start30 h31 c37 c42 c44 c46
  rcases group33 with ⟨h34,h35,h36,h37⟩
  have group38 := chunk7 a h37 h31 start31 h20 start17 h4 h15 start19 c46 c47 c48 c50 c52
  rcases group38 with ⟨h39,h40,h41,h42,h43⟩
  have group44 := chunk8 a h43 h41 h12 start22 h23 c52 c55 c56 c58
  rcases group44 with ⟨h45,h46,h47⟩
  have group48 := chunk9 a h47 h45 start21 h42 h40 start25 h26 c58 c60 c67 c68
  rcases group48 with ⟨h49,h50,h51,h52⟩
  have group53 := chunk10 a h52 h26 h35 start27 h39 c68 c70 c71 c77
  rcases group53 with ⟨h54,h55,h56,h57,h58⟩
  have group59 := chunk11 a start5 h30 h54 h55 h57 h51 c21 c68 c71 c75
  rcases group59 with ⟨h60,h61,h62,h63⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q64 | q65
  · have h66 : a 1 ∈ [0] := List.mem_singleton.mpr q64
    have group67 := chunk12 a start3 h66 h2 h8 h16 h29 h45 start4 h25 h42 h31 h20 h49 h3 h24 h30 h56 c5 c9 c10 c13 c14 c15 c17 c18 c19 c24 c26 c27 c30 c32 c33 c42
    rcases group67 with ⟨h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83⟩
    have group84 := chunk13 a h36 h82 h58 h77 h63 h78 h4 h76 h41 h73 h50 h61 h34 h62 c44 c46 c47 c50 c52 c60 c71 c72 c74
    rcases group84 with ⟨h85,h86,h87,h88,h89,h90,h91,h92,h93⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h66) (And.intro (forced (a 2) 0 h69) (And.intro (forced (a 3) 0 h68) (And.intro (forced (a 4) 0 h74) (And.intro (forced (a 5) 0 h60) (And.intro (forced (a 6) 0 h70) (And.intro (forced (a 7) 0 h71) (And.intro (forced (a 8) 0 h80) (And.intro (forced (a 9) 0 h81) (And.intro (forced (a 10) 0 h9) (And.intro (forced (a 11) 0 h72) (And.intro (forced (a 12) 0 h75) (And.intro (forced (a 13) 0 h82) (And.intro (forced (a 14) 0 h77) (And.intro (forced (a 15) 0 h78) (And.intro (forced (a 16) 0 h88) (And.intro (forced (a 17) 0 h89) (And.intro (forced (a 18) 0 h12) (And.intro (forced (a 19) 0 h73) (And.intro (forced (a 20) 0 h76) (And.intro (forced (a 21) 0 h90) (And.intro (forced (a 22) 0 h46) (And.intro (forced (a 23) 0 h79) (And.intro (forced (a 24) 0 h55) (And.intro (forced (a 25) 0 h91) (And.intro (forced (a 26) 0 h92) (And.intro (forced (a 27) 0 h93) (And.intro (forced (a 28) 0 h83) (And.intro (forced (a 29) 0 h85) (And.intro (forced (a 30) 0 h86) (forced (a 31) 0 h87))))))))))))))))))))))))))))))))
  · have h94 : a 1 ∈ [1] := List.mem_singleton.mpr q65
    have group95 := chunk14 a start3 h94 h2 h8 h16 h29 h45 start4 h25 h42 h31 h20 h49 h3 h24 h30 h56 c5 c9 c10 c13 c14 c15 c17 c18 c19 c24 c26 c27 c30 c32 c33 c42
    rcases group95 with ⟨h96,h97,h98,h99,h100,h101,h102,h103,h104,h105,h106,h107,h108,h109,h110,h111⟩
    have group112 := chunk15 a h36 h110 h58 h105 h63 h106 h4 h104 h41 h101 h50 h61 h34 h62 c44 c46 c47 c50 c52 c60 c71 c72 c74
    rcases group112 with ⟨h113,h114,h115,h116,h117,h118,h119,h120,h121⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h94) (And.intro (forced (a 2) 3 h97) (And.intro (forced (a 3) 1 h96) (And.intro (forced (a 4) 1 h102) (And.intro (forced (a 5) 0 h60) (And.intro (forced (a 6) 3 h98) (And.intro (forced (a 7) 3 h99) (And.intro (forced (a 8) 2 h108) (And.intro (forced (a 9) 2 h109) (And.intro (forced (a 10) 0 h9) (And.intro (forced (a 11) 2 h100) (And.intro (forced (a 12) 1 h103) (And.intro (forced (a 13) 1 h110) (And.intro (forced (a 14) 1 h105) (And.intro (forced (a 15) 2 h106) (And.intro (forced (a 16) 1 h116) (And.intro (forced (a 17) 1 h117) (And.intro (forced (a 18) 0 h12) (And.intro (forced (a 19) 6 h101) (And.intro (forced (a 20) 1 h104) (And.intro (forced (a 21) 1 h118) (And.intro (forced (a 22) 0 h46) (And.intro (forced (a 23) 1 h107) (And.intro (forced (a 24) 0 h55) (And.intro (forced (a 25) 2 h119) (And.intro (forced (a 26) 1 h120) (And.intro (forced (a 27) 2 h121) (And.intro (forced (a 28) 1 h111) (And.intro (forced (a 29) 1 h113) (And.intro (forced (a 30) 1 h114) (forced (a 31) 1 h115))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_207
