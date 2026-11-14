import PartitionData205_170
import PartitionPiece205_170_0
import PartitionPiece205_170_1
import PartitionPiece205_170_2
import PartitionPiece205_170_3
import PartitionPiece205_170_4
import PartitionPiece205_170_5
namespace PartitionCover205_170
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8])
    (start7 : a 7 ∈ [0,1,2])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start13 : a 13 ∈ [0,1,2,3])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start23 : a 23 ∈ [0,1,2])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start26 : a 26 ∈ [0,1,2,3,4,5])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
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
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0) := by
  have group1 := chunk0 a start4 start0 start8 start16 c2 c3 c4
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 start0 start5 start1 start9 start17 c4 c6 c7 c8
  rcases group5 with ⟨h6,h7,h8,h9⟩
  have group10 := chunk2 a h9 start1 start6 start2 start18 c8 c10 c12
  rcases group10 with ⟨h11,h12,h13⟩
  have group14 := chunk3 a start11 start3 start19 c14 c15
  rcases group14 with ⟨h15,h16⟩
  have group17 := chunk4 a h2 h7 h12 start12 c16 c17 c18
  rcases group17 with ⟨h18,h19,h20,h21⟩
  have group22 := chunk5 a h21 h18 start20 c18 c19
  rcases group22 with ⟨h23,h24⟩
  have group25 := chunk6 a h24 h18 start7 h19 start13 start21 h20 c19 c20 c21 c22 c23
  rcases group25 with ⟨h26,h27,h28,h29,h30⟩
  have group31 := chunk7 a start14 h30 start22 c24 c25
  rcases group31 with ⟨h32,h33⟩
  have group34 := chunk8 a h33 h30 c25
  have h35 := group34
  have group36 := chunk9 a h35 h30 start15 h27 c25 c26
  rcases group36 with ⟨h37,h38⟩
  have group39 := chunk10 a h38 h27 h8 h3 c26 c28
  rcases group39 with ⟨h40,h41⟩
  have group42 := chunk11 a h41 h3 start10 start24 c28 c29 c31
  rcases group42 with ⟨h43,h44,h45⟩
  have group46 := chunk12 a h45 h3 h15 h43 start25 c31 c32 c34
  rcases group46 with ⟨h47,h48,h49⟩
  have group50 := chunk13 a h49 h43 h32 h44 start26 h40 h48 start27 c34 c36 c37 c38 c39
  rcases group50 with ⟨h51,h52,h53,h54,h55⟩
  have group56 := chunk14 a h55 h48 h28 h23 h52 start28 c39 c40 c41 c42
  rcases group56 with ⟨h57,h58,h59,h60⟩
  have group61 := chunk15 a h60 h59 h58 h54 start29 start30 h52 c42 c43 c44 c46
  rcases group61 with ⟨h62,h63,h64,h65⟩
  have group66 := chunk16 a h65 h52 start31 h54 c46 c47
  rcases group66 with ⟨h67,h68⟩
  have group69 := chunk17 a h68 h54 h6 h11 h13 c47 c48 c49
  rcases group69 with ⟨h70,h71,h72⟩
  have group73 := chunk18 a h72 h71 h29 h11 h37 start23 h16 c49 c53 c56 c58
  rcases group73 with ⟨h74,h75,h76⟩
  have group77 := chunk19 a h16 h57 h26 h75 h37 h64 c59 c60 c61 c64
  rcases group77 with ⟨h78,h79,h80,h81,h82⟩
  have group83 := chunk20 a h82 h75 h67 h81 h70 h76 h47 h51 h53 h79 h62 c64 c66 c67 c68 c69 c72 c73 c74 c75 c76
  rcases group83 with ⟨h84,h85,h86,h87,h88,h89⟩
  have group90 := chunk21 a start2 h30 h43 h88 h11 h78 h71 h74 c10 c34 c48 c49 c52
  rcases group90 with ⟨h91,h92,h93,h94,h95⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h91) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h18) (And.intro (forced (a 5) 0 h19) (And.intro (forced (a 6) 0 h30) (And.intro (forced (a 7) 0 h27) (And.intro (forced (a 8) 0 h3) (And.intro (forced (a 9) 0 h92) (And.intro (forced (a 10) 0 h44) (And.intro (forced (a 11) 0 h48) (And.intro (forced (a 12) 0 h59) (And.intro (forced (a 13) 0 h63) (And.intro (forced (a 14) 0 h52) (And.intro (forced (a 15) 0 h54) (And.intro (forced (a 16) 0 h94) (And.intro (forced (a 17) 0 h93) (And.intro (forced (a 18) 0 h95) (And.intro (forced (a 19) 0 h78) (And.intro (forced (a 20) 0 h80) (And.intro (forced (a 21) 0 h75) (And.intro (forced (a 22) 0 h81) (And.intro (forced (a 23) 0 h76) (And.intro (forced (a 24) 0 h87) (And.intro (forced (a 25) 0 h88) (And.intro (forced (a 26) 0 h53) (And.intro (forced (a 27) 0 h89) (And.intro (forced (a 28) 0 h62) (And.intro (forced (a 29) 0 h84) (And.intro (forced (a 30) 0 h85) (forced (a 31) 0 h86)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_170
