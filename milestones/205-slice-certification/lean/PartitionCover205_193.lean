import PartitionData205_193
import PartitionPiece205_193_0
import PartitionPiece205_193_1
import PartitionPiece205_193_2
import PartitionPiece205_193_3
import PartitionPiece205_193_4
namespace PartitionCover205_193
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7])
    (start5 : a 5 ∈ [0,1,2])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0,1,2,3])
    (start8 : a 8 ∈ [0,1,2,3,4,5])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start13 : a 13 ∈ [0,1,2,3,4,5])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8])
    (start22 : a 22 ∈ [0,1,2,3])
    (start23 : a 23 ∈ [0,1,2,3,4,5])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start27 : a 27 ∈ [0,1,2,3,4,5])
    (start28 : a 28 ∈ [0,1,2,3])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=2 ∧ a 3=1 ∧ a 4=4 ∧ a 5=1 ∧ a 6=1 ∧ a 7=2 ∧ a 8=3 ∧ a 9=3 ∧ a 10=6 ∧ a 11=0 ∧ a 12=6 ∧ a 13=3 ∧ a 14=6 ∧ a 15=0 ∧ a 16=3 ∧ a 17=3 ∧ a 18=6 ∧ a 19=0 ∧ a 20=6 ∧ a 21=3 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=6 ∧ a 26=6 ∧ a 27=3 ∧ a 28=0 ∧ a 29=6 ∧ a 30=6 ∧ a 31=1) := by
  have group1 := chunk0 a start2 start0 start4 start8 start16 c1 c2 c3 c4
  rcases group1 with ⟨h2,h3,h4,h5⟩
  have group6 := chunk1 a h5 start0 start9 start1 start17 start18 h2 c4 c7 c8 c12
  rcases group6 with ⟨h7,h8,h9,h10⟩
  have group11 := chunk2 a h10 h2 start11 start3 start19 c12 c14 c15
  rcases group11 with ⟨h12,h13,h14⟩
  have group15 := chunk3 a h14 start3 start12 h3 start20 c15 c18 c19
  rcases group15 with ⟨h16,h17,h18⟩
  have group19 := chunk4 a h18 h3 start13 start5 h8 h4 start10 h17 c19 c21 c28 c29 c30
  rcases group19 with ⟨h20,h21,h22,h23,h24⟩
  have group25 := chunk5 a start24 h4 h13 h22 h21 h23 start14 c31 c32 c33 c35 c36
  rcases group25 with ⟨h26,h27,h28,h29,h30⟩
  have group31 := chunk6 a h30 h29 start15 h27 start27 start28 h24 c36 c38 c39 c42
  rcases group31 with ⟨h32,h33,h34,h35⟩
  have group36 := chunk7 a h35 h24 start29 h28 start30 h32 c42 c44 c46
  rcases group36 with ⟨h37,h38,h39⟩
  have group40 := chunk8 a h39 h32 start31 h33 h9 h7 h12 c46 c47 c48 c49
  rcases group40 with ⟨h41,h42,h43,h44⟩
  have group45 := chunk9 a h44 h7 h20 start21 h43 c49 c50 c53
  rcases group45 with ⟨h46,h47,h48⟩
  have group49 := chunk10 a h48 h43 h16 h46 start22 start26 start23 c53 c55 c56 c57 c58 c63
  rcases group49 with ⟨h50,h51,h52,h53,h54⟩
  have group55 := chunk11 a h54 h50 h38 start25 h26 h53 c63 c64 c68 c69 c72
  rcases group55 with ⟨h56,h57,h58,h59,h60⟩
  have group61 := chunk12 a start5 h28 start7 h33 c21 c26
  rcases group61 with ⟨h62,h63⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q64 | q65
  · have h66 : a 1 ∈ [0] := List.mem_singleton.mpr q64
    have group67 := chunk13 a start3 h66 h2 start6 h63 h3 h24 h47 h32 h4 h29 h28 h57 h41 h7 h50 h58 c5 c9 c10 c13 c17 c18 c19 c24 c30 c36 c40 c44 c46 c50 c60 c72
    rcases group67 with ⟨h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83⟩
    have group84 := chunk14 a h60 h80 h42 h62 h72 h22 h76 h43 h81 h46 h34 h83 c16 c28 c48 c49 c71 c74 c79
    rcases group84 with ⟨h85,h86,h87,h88,h89,h90,h91⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h66) (And.intro (forced (a 2) 0 h69) (And.intro (forced (a 3) 0 h68) (And.intro (forced (a 4) 0 h72) (And.intro (forced (a 5) 0 h87) (And.intro (forced (a 6) 0 h70) (And.intro (forced (a 7) 0 h71) (And.intro (forced (a 8) 0 h76) (And.intro (forced (a 9) 0 h88) (And.intro (forced (a 10) 0 h77) (And.intro (forced (a 11) 0 h27) (And.intro (forced (a 12) 0 h73) (And.intro (forced (a 13) 0 h78) (And.intro (forced (a 14) 0 h75) (And.intro (forced (a 15) 0 h33) (And.intro (forced (a 16) 0 h81) (And.intro (forced (a 17) 0 h89) (And.intro (forced (a 18) 0 h90) (And.intro (forced (a 19) 0 h51) (And.intro (forced (a 20) 0 h74) (And.intro (forced (a 21) 0 h82) (And.intro (forced (a 22) 0 h52) (And.intro (forced (a 23) 0 h56) (And.intro (forced (a 24) 0 h59) (And.intro (forced (a 25) 0 h83) (And.intro (forced (a 26) 0 h85) (And.intro (forced (a 27) 0 h91) (And.intro (forced (a 28) 0 h37) (And.intro (forced (a 29) 0 h79) (And.intro (forced (a 30) 0 h80) (forced (a 31) 0 h86))))))))))))))))))))))))))))))))
  · have h92 : a 1 ∈ [1] := List.mem_singleton.mpr q65
    have group93 := chunk15 a start3 h92 h2 start6 h63 h3 h24 h47 h32 h4 h29 h28 h57 h41 h7 h50 h58 c5 c9 c10 c13 c17 c18 c19 c24 c30 c36 c40 c44 c46 c50 c60 c72
    rcases group93 with ⟨h94,h95,h96,h97,h98,h99,h100,h101,h102,h103,h104,h105,h106,h107,h108,h109⟩
    have group110 := chunk16 a h60 h106 h42 h62 h98 h22 h102 h43 h107 h46 h34 h109 c16 c28 c48 c49 c71 c74 c79
    rcases group110 with ⟨h111,h112,h113,h114,h115,h116,h117⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h92) (And.intro (forced (a 2) 2 h95) (And.intro (forced (a 3) 1 h94) (And.intro (forced (a 4) 4 h98) (And.intro (forced (a 5) 1 h113) (And.intro (forced (a 6) 1 h96) (And.intro (forced (a 7) 2 h97) (And.intro (forced (a 8) 3 h102) (And.intro (forced (a 9) 3 h114) (And.intro (forced (a 10) 6 h103) (And.intro (forced (a 11) 0 h27) (And.intro (forced (a 12) 6 h99) (And.intro (forced (a 13) 3 h104) (And.intro (forced (a 14) 6 h101) (And.intro (forced (a 15) 0 h33) (And.intro (forced (a 16) 3 h107) (And.intro (forced (a 17) 3 h115) (And.intro (forced (a 18) 6 h116) (And.intro (forced (a 19) 0 h51) (And.intro (forced (a 20) 6 h100) (And.intro (forced (a 21) 3 h108) (And.intro (forced (a 22) 0 h52) (And.intro (forced (a 23) 0 h56) (And.intro (forced (a 24) 0 h59) (And.intro (forced (a 25) 6 h109) (And.intro (forced (a 26) 6 h111) (And.intro (forced (a 27) 3 h117) (And.intro (forced (a 28) 0 h37) (And.intro (forced (a 29) 6 h105) (And.intro (forced (a 30) 6 h106) (forced (a 31) 1 h112))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_193
