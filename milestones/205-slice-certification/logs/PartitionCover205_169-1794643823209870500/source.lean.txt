import PartitionData205_169
import PartitionPiece205_169_0
import PartitionPiece205_169_1
import PartitionPiece205_169_2
import PartitionPiece205_169_3
namespace PartitionCover205_169
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8])
    (start7 : a 7 ∈ [0,1,2])
    (start8 : a 8 ∈ [0,1,2,3,4,5])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2])
    (start13 : a 13 ∈ [0])
    (start14 : a 14 ∈ [0,1,2,3,4,5])
    (start15 : a 15 ∈ [0,1,2,3,4,5])
    (start16 : a 16 ∈ [0,1,2,3,4,5])
    (start17 : a 17 ∈ [0,1,2,3,4,5])
    (start18 : a 18 ∈ [0,1,2])
    (start19 : a 19 ∈ [0,1,2,3,4,5])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start24 : a 24 ∈ [0,1,2])
    (start25 : a 25 ∈ [0,1,2])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start27 : a 27 ∈ [0,1,2,3,4,5])
    (start28 : a 28 ∈ [0,1,2,3,4,5])
    (start29 : a 29 ∈ [0,1,2,3,4,5])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start31 : a 31 ∈ [0,1,2,3,4,5])
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
      (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=7 ∧ a 5=13 ∧ a 6=2 ∧ a 7=2 ∧ a 8=5 ∧ a 9=5 ∧ a 10=5 ∧ a 11=5 ∧ a 12=0 ∧ a 13=0 ∧ a 14=1 ∧ a 15=5 ∧ a 16=5 ∧ a 17=5 ∧ a 18=2 ∧ a 19=2 ∧ a 20=8 ∧ a 21=0 ∧ a 22=4 ∧ a 23=4 ∧ a 24=0 ∧ a 25=0 ∧ a 26=5 ∧ a 27=1 ∧ a 28=1 ∧ a 29=1 ∧ a 30=2 ∧ a 31=2) := by
  have group1 := chunk0 a start4 start0 start8 start16 start5 start1 c2 c3 c4 c6
  rcases group1 with ⟨h2,h3,h4,h5⟩
  have group6 := chunk1 a h5 start1 start9 start17 start6 start2 c6 c7 c8 c10
  rcases group6 with ⟨h7,h8,h9,h10⟩
  have group11 := chunk2 a h10 start2 start19 start3 h2 h7 start12 start20 c10 c15 c16 c17 c18 c19
  rcases group11 with ⟨h12,h13,h14,h15,h16,h17⟩
  have group18 := chunk3 a h17 h14 start7 h15 start21 c19 c20 c22
  rcases group18 with ⟨h19,h20,h21⟩
  have group22 := chunk4 a h21 h15 h12 h20 start14 start22 c22 c23 c24 c25
  rcases group22 with ⟨h23,h24,h25,h26⟩
  have group27 := chunk5 a h26 h24 start15 h20 start23 h3 h8 c25 c26 c27 c28
  rcases group27 with ⟨h28,h29,h30,h31⟩
  have group32 := chunk6 a start10 h31 start11 h8 start25 h25 start26 c29 c32 c34 c36 c37
  rcases group32 with ⟨h33,h34,h35,h36⟩
  have group37 := chunk7 a h36 h33 h34 h29 start27 start28 h16 c37 c38 c39 c42
  rcases group37 with ⟨h38,h39,h40,h41,h42⟩
  have group43 := chunk8 a start30 h25 h4 h9 start18 h19 h28 h38 h30 h13 c46 c48 c49 c50 c56 c57 c58
  rcases group43 with ⟨h44,h45,h46,h47,h48,h49,h50⟩
  have group51 := chunk9 a h50 h13 h41 h47 h23 start29 h44 h48 start31 c58 c59 c60 c64 c66 c67
  rcases group51 with ⟨h52,h53,h54,h55,h56,h57,h58⟩
  have group59 := chunk10 a h58 h52 start24 h35 h56 h57 h49 c67 c68 c72 c74
  rcases group59 with ⟨h60,h61,h62,h63⟩
  rcases (show a 4=0 ∨ a 4=7 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h14) with q64 | q65
  · have h66 : a 4 ∈ [0] := List.mem_singleton.mpr q64
    have group67 := chunk11 a h15 h66 h24 h54 h20 h25 h48 h40 h33 h49 h39 h53 h63 h60 h45 h46 c16 c17 c19 c20 c24 c25 c26 c36 c37 c38 c39 c46 c47 c50 c56
    rcases group67 with ⟨h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82⟩
    have group83 := chunk12 a h13 h78 h42 h70 h52 h73 h80 h62 h31 h75 h8 h77 h9 h81 c29 c32 c48 c59 c62 c65 c67 c76
    rcases group83 with ⟨h84,h85,h86,h87,h88,h89,h90,h91⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h66) (And.intro (forced (a 5) 0 h68) (And.intro (forced (a 6) 0 h69) (And.intro (forced (a 7) 0 h71) (And.intro (forced (a 8) 0 h89) (And.intro (forced (a 9) 0 h90) (And.intro (forced (a 10) 0 h75) (And.intro (forced (a 11) 0 h77) (And.intro (forced (a 12) 0 h16) (And.intro (forced (a 13) 0 start13) (And.intro (forced (a 14) 0 h72) (And.intro (forced (a 15) 0 h74) (And.intro (forced (a 16) 0 h81) (And.intro (forced (a 17) 0 h91) (And.intro (forced (a 18) 0 h82) (And.intro (forced (a 19) 0 h84) (And.intro (forced (a 20) 0 h70) (And.intro (forced (a 21) 0 h55) (And.intro (forced (a 22) 0 h73) (And.intro (forced (a 23) 0 h86) (And.intro (forced (a 24) 0 h61) (And.intro (forced (a 25) 0 h35) (And.intro (forced (a 26) 0 h76) (And.intro (forced (a 27) 0 h78) (And.intro (forced (a 28) 0 h85) (And.intro (forced (a 29) 0 h88) (And.intro (forced (a 30) 0 h79) (forced (a 31) 0 h87))))))))))))))))))))))))))))))))
  · have h92 : a 4 ∈ [7] := List.mem_singleton.mpr q65
    have group93 := chunk13 a h15 h92 h24 h54 h20 h25 h48 h40 h33 h49 h39 h53 h63 h60 h45 h46 c16 c17 c19 c20 c24 c25 c26 c36 c37 c38 c39 c46 c47 c50 c56
    rcases group93 with ⟨h94,h95,h96,h97,h98,h99,h100,h101,h102,h103,h104,h105,h106,h107,h108⟩
    have group109 := chunk14 a h13 h104 h42 h96 h52 h99 h106 h62 h31 h101 h8 h103 h9 h107 c29 c32 c48 c59 c62 c65 c67 c76
    rcases group109 with ⟨h110,h111,h112,h113,h114,h115,h116,h117⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 7 h92) (And.intro (forced (a 5) 13 h94) (And.intro (forced (a 6) 2 h95) (And.intro (forced (a 7) 2 h97) (And.intro (forced (a 8) 5 h115) (And.intro (forced (a 9) 5 h116) (And.intro (forced (a 10) 5 h101) (And.intro (forced (a 11) 5 h103) (And.intro (forced (a 12) 0 h16) (And.intro (forced (a 13) 0 start13) (And.intro (forced (a 14) 1 h98) (And.intro (forced (a 15) 5 h100) (And.intro (forced (a 16) 5 h107) (And.intro (forced (a 17) 5 h117) (And.intro (forced (a 18) 2 h108) (And.intro (forced (a 19) 2 h110) (And.intro (forced (a 20) 8 h96) (And.intro (forced (a 21) 0 h55) (And.intro (forced (a 22) 4 h99) (And.intro (forced (a 23) 4 h112) (And.intro (forced (a 24) 0 h61) (And.intro (forced (a 25) 0 h35) (And.intro (forced (a 26) 5 h102) (And.intro (forced (a 27) 1 h104) (And.intro (forced (a 28) 1 h111) (And.intro (forced (a 29) 1 h114) (And.intro (forced (a 30) 2 h105) (forced (a 31) 2 h113))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_169
