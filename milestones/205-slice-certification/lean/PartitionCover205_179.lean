import PartitionData205_179
import PartitionPiece205_179_0
import PartitionPiece205_179_1
import PartitionPiece205_179_2
import PartitionPiece205_179_3
namespace PartitionCover205_179
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1,2])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0])
    (start5 : a 5 ∈ [0,1,2])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0,1,2])
    (start8 : a 8 ∈ [0,1,2,3,4,5])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2,3,4,5])
    (start13 : a 13 ∈ [0,1,2])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start19 : a 19 ∈ [0,1,2,3])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start26 : a 26 ∈ [0,1,2,3,4,5])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start30 : a 30 ∈ [0,1,2,3])
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
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0) := by
  have group1 := chunk0 a start2 start3 start6 start10 start18 c9 c10 c11 c12
  rcases group1 with ⟨h2,h3,h4,h5⟩
  have group6 := chunk1 a h5 h2 start11 start3 start19 start5 start4 start12 start20 c12 c14 c15 c16 c18 c19
  rcases group6 with ⟨h7,h8,h9,h10,h11,h12⟩
  have group13 := chunk2 a h12 start4 start13 h10 start21 start7 h3 start14 start22 c19 c21 c22 c23 c24 c25
  rcases group13 with ⟨h14,h15,h16,h17,h18,h19⟩
  have group20 := chunk3 a h19 h3 start15 h17 start23 c25 c26 c27
  rcases group20 with ⟨h21,h22,h23⟩
  have group24 := chunk4 a h23 h17 start8 h4 h11 start9 h8 h18 start26 c27 c29 c30 c32 c36 c37
  rcases group24 with ⟨h25,h26,h27,h28,h29,h30⟩
  have group31 := chunk5 a h30 h4 h22 h8 start27 h27 h29 start28 c37 c38 c39 c41 c42
  rcases group31 with ⟨h32,h33,h34,h35,h36⟩
  have group37 := chunk6 a h36 h35 h33 h15 start29 start30 h29 start31 c42 c43 c44 c46 c47
  rcases group37 with ⟨h38,h39,h40,h41,h42,h43⟩
  have group44 := chunk7 a h43 h39 start16 h7 c47 c49
  rcases group44 with ⟨h45,h46⟩
  have group47 := chunk8 a h46 h7 h14 start17 h9 c49 c50 c52
  rcases group47 with ⟨h48,h49,h50⟩
  have group51 := chunk9 a h50 h9 h16 h7 h21 h32 c52 c53 c55 c56 c57
  rcases group51 with ⟨h52,h53,h54,h55,h56,h57⟩
  have group58 := chunk10 a h25 h54 h53 h49 c58 c60 c63
  rcases group58 with ⟨h59,h60⟩
  have group61 := chunk11 a h59 h60 h45 start24 h57 h38 start25 h34 c63 c67 c69 c70 c71
  rcases group61 with ⟨h62,h63,h64,h65,h66⟩
  have group67 := chunk12 a h66 h34 h41 h63 h65 h42 h10 h60 c22 c71 c72 c75 c77
  rcases group67 with ⟨h68,h69,h70,h71,h72⟩
  have group73 := chunk13 a h17 h39 h26 h28 h48 h52 h60 h62 h64 h71 h68 h70 h69 c26 c28 c48 c63 c70 c71 c72
  rcases group73 with ⟨h74,h75,h76,h77,h78,h79,h80,h81⟩
  have group82 := chunk14 a h77 h78 h76 h55 c48 c49 c53
  rcases group82 with ⟨h83,h84,h85⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 start4) (And.intro (forced (a 5) 0 h72) (And.intro (forced (a 6) 0 h3) (And.intro (forced (a 7) 0 h74) (And.intro (forced (a 8) 0 h75) (And.intro (forced (a 9) 0 h28) (And.intro (forced (a 10) 0 h4) (And.intro (forced (a 11) 0 h8) (And.intro (forced (a 12) 0 h35) (And.intro (forced (a 13) 0 h40) (And.intro (forced (a 14) 0 h29) (And.intro (forced (a 15) 0 h39) (And.intro (forced (a 16) 0 h84) (And.intro (forced (a 17) 0 h83) (And.intro (forced (a 18) 0 h85) (And.intro (forced (a 19) 0 h54) (And.intro (forced (a 20) 0 h49) (And.intro (forced (a 21) 0 h78) (And.intro (forced (a 22) 0 h56) (And.intro (forced (a 23) 0 h62) (And.intro (forced (a 24) 0 h79) (And.intro (forced (a 25) 0 h80) (And.intro (forced (a 26) 0 h57) (And.intro (forced (a 27) 0 h70) (And.intro (forced (a 28) 0 h71) (And.intro (forced (a 29) 0 h81) (And.intro (forced (a 30) 0 h42) (forced (a 31) 0 h63)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_179
