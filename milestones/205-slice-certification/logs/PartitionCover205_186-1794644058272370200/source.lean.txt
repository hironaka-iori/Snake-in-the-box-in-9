import PartitionData205_186
import PartitionPiece205_186_0
import PartitionPiece205_186_1
import PartitionPiece205_186_2
import PartitionPiece205_186_3
namespace PartitionCover205_186
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2])
    (start2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start8 : a 8 ∈ [0])
    (start9 : a 9 ∈ [0,1,2,3])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1,2,3])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start24 : a 24 ∈ [0,1,2,3])
    (start25 : a 25 ∈ [0,1,2,3])
    (start26 : a 26 ∈ [0,1,2])
    (start27 : a 27 ∈ [0,1,2,3,4,5])
    (start28 : a 28 ∈ [0,1])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7])
    (start30 : a 30 ∈ [0,1])
    (start31 : a 31 ∈ [0,1,2,3])
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
  have group1 := chunk0 a start2 start0 start16 start5 start1 c1 c4 c6
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 start1 start9 start17 start3 h2 c6 c7 c8 c9
  rcases group5 with ⟨h6,h7,h8,h9,h10⟩
  have group11 := chunk2 a h10 h2 start6 c9 c10
  rcases group11 with ⟨h12,h13⟩
  have group14 := chunk3 a h13 h2 start10 c10 c11
  rcases group14 with ⟨h15,h16⟩
  have group17 := chunk4 a h16 h2 start18 c11 c12
  rcases group17 with ⟨h18,h19⟩
  have group20 := chunk5 a h19 h2 h12 start7 c12 c13
  rcases group20 with ⟨h21,h22,h23⟩
  have group24 := chunk6 a h23 h22 start11 start19 c13 c14 c15
  rcases group24 with ⟨h25,h26,h27⟩
  have group28 := chunk7 a h27 h22 start4 h15 start12 start20 c15 c17 c18 c19
  rcases group28 with ⟨h29,h30,h31,h32,h33⟩
  have group34 := chunk8 a h33 h30 h6 h25 start13 start21 h31 start14 c19 c20 c21 c22 c23 c24
  rcases group34 with ⟨h35,h36,h37,h38,h39,h40,h41⟩
  have group42 := chunk9 a h41 h40 start22 start15 h37 c24 c25 c26
  rcases group42 with ⟨h43,h44,h45⟩
  have group46 := chunk10 a h45 h37 start23 c26 c27
  rcases group46 with ⟨h47,h48⟩
  have group49 := chunk11 a h48 h37 h18 start8 h26 h8 h38 start25 c27 c29 c32 c33 c34
  rcases group49 with ⟨h50,h51,h52,h53,h54⟩
  have group55 := chunk12 a h51 h52 start26 h47 start27 start28 h32 h53 start29 c35 c37 c38 c39 c42 c43 c44
  rcases group55 with ⟨h56,h57,h58,h59,h60,h61,h62⟩
  have group63 := chunk13 a h62 h53 start30 h43 start31 h59 h9 h3 h35 h39 h29 h21 h44 c44 c46 c47 c48 c50 c53 c55 c56
  rcases group63 with ⟨h64,h65,h66,h67,h68,h69,h70,h71,h72⟩
  have group73 := chunk14 a h72 h44 h58 h50 h71 h60 h70 h69 h64 h66 c56 c57 c58 c59 c60 c64 c65 c67
  rcases group73 with ⟨h74,h75,h76,h77,h78,h79,h80⟩
  have group81 := chunk15 a start24 h54 h64 h7 h22 h67 h2 h37 h36 h30 h8 h57 h78 c5 c8 c9 c13 c16 c32 c52 c68 c72
  rcases group81 with ⟨h82,h83,h84,h85,h86,h87,h88,h89,h90,h91⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h85) (And.intro (forced (a 2) 0 h88) (And.intro (forced (a 3) 0 h86) (And.intro (forced (a 4) 0 h30) (And.intro (forced (a 5) 0 h90) (And.intro (forced (a 6) 0 h40) (And.intro (forced (a 7) 0 h89) (And.intro (forced (a 8) 0 start8) (And.intro (forced (a 9) 0 h91) (And.intro (forced (a 10) 0 h56) (And.intro (forced (a 11) 0 h57) (And.intro (forced (a 12) 0 h32) (And.intro (forced (a 13) 0 h53) (And.intro (forced (a 14) 0 h43) (And.intro (forced (a 15) 0 h59) (And.intro (forced (a 16) 0 h68) (And.intro (forced (a 17) 0 h87) (And.intro (forced (a 18) 0 h74) (And.intro (forced (a 19) 0 h78) (And.intro (forced (a 20) 0 h69) (And.intro (forced (a 21) 0 h79) (And.intro (forced (a 22) 0 h75) (And.intro (forced (a 23) 0 h77) (And.intro (forced (a 24) 0 h82) (And.intro (forced (a 25) 0 h83) (And.intro (forced (a 26) 0 h76) (And.intro (forced (a 27) 0 h60) (And.intro (forced (a 28) 0 h61) (And.intro (forced (a 29) 0 h84) (And.intro (forced (a 30) 0 h65) (forced (a 31) 0 h80)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_186
