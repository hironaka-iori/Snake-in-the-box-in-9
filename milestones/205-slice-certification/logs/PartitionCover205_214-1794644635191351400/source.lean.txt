import PartitionData205_214
import PartitionPiece205_214_0
import PartitionPiece205_214_1
import PartitionPiece205_214_2
import PartitionPiece205_214_3
namespace PartitionCover205_214
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1,2,3])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0,1,2])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2,3,4,5])
    (start13 : a 13 ∈ [0,1,2,3,4,5])
    (start14 : a 14 ∈ [0,1,2,3,4,5])
    (start15 : a 15 ∈ [0])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start17 : a 17 ∈ [0,1,2,3,4,5])
    (start18 : a 18 ∈ [0,1,2,3,4,5])
    (start19 : a 19 ∈ [0,1,2,3,4,5])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5])
    (start23 : a 23 ∈ [0])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8])
    (start27 : a 27 ∈ [0,1,2,3,4,5])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start29 : a 29 ∈ [0,1,2,3,4,5])
    (start30 : a 30 ∈ [0,1,2,3,4,5])
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
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0) := by
  have group1 := chunk0 a start2 start0 start4 start8 c1 c2 c3
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 start0 start16 c3 c4
  rcases group5 with ⟨h6,h7⟩
  have group8 := chunk2 a h7 start0 h2 start3 start6 start10 start18 start7 c4 c9 c10 c11 c12 c13
  rcases group8 with ⟨h9,h10,h11,h12,h13,h14,h15⟩
  have group16 := chunk3 a h15 h11 start11 start19 start5 h3 start12 c13 c14 c15 c16 c18
  rcases group16 with ⟨h17,h18,h19,h20,h21⟩
  have group22 := chunk4 a h21 h3 start20 h17 h20 start13 c18 c19 c20 c21
  rcases group22 with ⟨h23,h24,h25,h26⟩
  have group27 := chunk5 a h26 h20 start21 start22 h12 h6 start9 c21 c22 c25 c28
  rcases group27 with ⟨h28,h29,h30,h31,h32⟩
  have group33 := chunk6 a h31 h23 start24 c30 c31
  rcases group33 with ⟨h34,h35⟩
  have group36 := chunk7 a h35 h34 h32 h28 start25 start14 h13 c31 c33 c34 c36
  rcases group36 with ⟨h37,h38,h39,h40,h41⟩
  have group42 := chunk8 a h41 h13 start26 start27 h18 h23 start28 c36 c37 c39 c41 c42
  rcases group42 with ⟨h43,h44,h45,h46⟩
  have group47 := chunk9 a h46 h23 start29 h39 c42 c44
  rcases group47 with ⟨h48,h49⟩
  have group50 := chunk10 a h49 h39 start30 h43 h9 start17 h24 h29 c44 c46 c48 c50 c53
  rcases group50 with ⟨h51,h52,h53,h54⟩
  have group55 := chunk11 a h29 h54 h48 h24 h44 h37 h40 h51 h52 start31 h45 h11 h25 c13 c53 c62 c69 c70 c72 c74 c75 c78
  rcases group55 with ⟨h56,h57,h58,h59,h60,h61,h62,h63⟩
  have group64 := chunk12 a h18 h63 h19 h20 h39 h13 h34 h45 h14 h58 start1 h10 h30 c5 c9 c14 c15 c21 c29 c39 c56 c57
  rcases group64 with ⟨h65,h66,h67,h68,h69,h70,h71,h72,h73⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h71) (And.intro (forced (a 2) 0 h72) (And.intro (forced (a 3) 0 h63) (And.intro (forced (a 4) 0 h3) (And.intro (forced (a 5) 0 h67) (And.intro (forced (a 6) 0 h12) (And.intro (forced (a 7) 0 h25) (And.intro (forced (a 8) 0 h34) (And.intro (forced (a 9) 0 h38) (And.intro (forced (a 10) 0 h68) (And.intro (forced (a 11) 0 h65) (And.intro (forced (a 12) 0 h23) (And.intro (forced (a 13) 0 h39) (And.intro (forced (a 14) 0 h43) (And.intro (forced (a 15) 0 start15) (And.intro (forced (a 16) 0 h53) (And.intro (forced (a 17) 0 h54) (And.intro (forced (a 18) 0 h70) (And.intro (forced (a 19) 0 h66) (And.intro (forced (a 20) 0 h24) (And.intro (forced (a 21) 0 h56) (And.intro (forced (a 22) 0 h73) (And.intro (forced (a 23) 0 start23) (And.intro (forced (a 24) 0 h59) (And.intro (forced (a 25) 0 h60) (And.intro (forced (a 26) 0 h58) (And.intro (forced (a 27) 0 h69) (And.intro (forced (a 28) 0 h57) (And.intro (forced (a 29) 0 h61) (And.intro (forced (a 30) 0 h52) (forced (a 31) 0 h62)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_214
