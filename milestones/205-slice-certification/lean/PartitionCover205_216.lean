import PartitionData205_216
import PartitionPiece205_216_0
import PartitionPiece205_216_1
import PartitionPiece205_216_2
import PartitionPiece205_216_3
import PartitionPiece205_216_4
import PartitionPiece205_216_5
import PartitionPiece205_216_6
import PartitionPiece205_216_7
namespace PartitionCover205_216
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2])
    (start2 : a 2 ∈ [0,1,2,3])
    (start3 : a 3 ∈ [0,1,2])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start19 : a 19 ∈ [0,1,2,3,4,5])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start23 : a 23 ∈ [0,1,2,3])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
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
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0) := by
  have group1 := chunk0 a start2 start0 start4 c1 c2
  rcases group1 with ⟨h2,h3⟩
  have group4 := chunk1 a h3 start0 start8 start16 c2 c3 c4
  rcases group4 with ⟨h5,h6,h7⟩
  have group8 := chunk2 a h7 start0 c4
  have h9 := group8
  have group10 := chunk3 a h9 start0 start5 start1 c4 c6
  rcases group10 with ⟨h11,h12⟩
  have group13 := chunk4 a start9 start1 start17 c7 c8
  rcases group13 with ⟨h14,h15⟩
  have group16 := chunk5 a h15 start1 h2 start3 start6 c8 c9 c10
  rcases group16 with ⟨h17,h18,h19⟩
  have group20 := chunk6 a h19 h18 start10 h5 c10 c11 c17
  rcases group20 with ⟨h21,h22,h23⟩
  have group24 := chunk7 a h21 h23 start12 c17 c18
  rcases group24 with ⟨h25,h26⟩
  have group27 := chunk8 a h26 h23 start20 c18 c19
  rcases group27 with ⟨h28,h29⟩
  have group30 := chunk9 a h29 h23 start7 h12 c19 c20
  rcases group30 with ⟨h31,h32⟩
  have group33 := chunk10 a h32 h12 start13 c20 c21
  rcases group33 with ⟨h34,h35⟩
  have group36 := chunk11 a h35 h12 start21 c21 c22
  rcases group36 with ⟨h37,h38⟩
  have group39 := chunk12 a h38 h12 start14 h25 start22 c22 c24 c25
  rcases group39 with ⟨h40,h41,h42⟩
  have group43 := chunk13 a h42 h25 c25
  have h44 := group43
  have group45 := chunk14 a h44 h25 start15 h34 start23 h6 h14 h22 start24 c25 c26 c27 c28 c29 c31
  rcases group45 with ⟨h46,h47,h48,h49,h50,h51⟩
  have group52 := chunk15 a h51 h49 start11 h14 c31 c32
  rcases group52 with ⟨h53,h54⟩
  have group55 := chunk16 a h37 h14 start25 c33 c34
  rcases group55 with ⟨h56,h57⟩
  have group58 := chunk17 a h50 h54 start26 h47 start27 c35 c37 c38 c39
  rcases group58 with ⟨h59,h60,h61,h62,h63⟩
  have group64 := chunk18 a h63 h60 h28 h56 h41 start28 c39 c40 c41 c42
  rcases group64 with ⟨h65,h66,h67⟩
  have group68 := chunk19 a h67 h66 c42
  have h69 := group68
  have group70 := chunk20 a h69 h66 h62 h56 start29 c42 c43 c44
  rcases group70 with ⟨h71,h72,h73⟩
  have group74 := chunk21 a h73 h56 h72 h41 start30 c44 c45 c46
  rcases group74 with ⟨h75,h76,h77⟩
  have group78 := chunk22 a h77 h41 start31 h76 c46 c47
  rcases group78 with ⟨h79,h80⟩
  have group81 := chunk23 a h80 h76 h17 h11 start18 h31 c47 c48 c49 c50
  rcases group81 with ⟨h82,h83,h84,h85⟩
  have group86 := chunk24 a h53 h11 start19 h83 h40 h57 h84 h46 h48 h65 c51 c52 c53 c54 c55 c56 c58 c59
  rcases group86 with ⟨h87,h88,h89,h90,h91,h92,h93,h94⟩
  have group95 := chunk25 a h85 h89 h92 h75 h93 h87 h61 h71 h79 h82 h94 c60 c61 c64 c65 c69 c70 c74 c75
  rcases group95 with ⟨h96,h97,h98,h99,h100,h101⟩
  have group102 := chunk26 a h98 h71 h100 h101 start1 h83 h18 h59 start3 h60 h23 h66 h25 h97 h34 h76 c8 c11 c14 c18 c25 c26 c76 c77 c79
  rcases group102 with ⟨h103,h104,h105,h106,h107,h108,h109,h110⟩
  have group111 := chunk27 a h110 h76 h49 h59 h66 h14 h60 h56 h90 h11 h99 h83 h88 h91 h97 c26 c29 c30 c32 c33 c34 c43 c51 c52 c56
  rcases group111 with ⟨h112,h113,h114,h115,h116,h117,h118,h119,h120⟩
  have group121 := chunk28 a h120 h97 h89 h103 h61 h104 h71 h105 h107 h12 h112 h108 h109 h118 c5 c6 c13 c17 c20 c49 c56 c64 c74 c77
  rcases group121 with ⟨h122,h123,h124,h125,h126,h127,h128,h129,h130⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h126) (And.intro (forced (a 2) 0 h106) (And.intro (forced (a 3) 0 h107) (And.intro (forced (a 4) 0 h129) (And.intro (forced (a 5) 0 h127) (And.intro (forced (a 6) 0 h109) (And.intro (forced (a 7) 0 h128) (And.intro (forced (a 8) 0 h113) (And.intro (forced (a 9) 0 h114) (And.intro (forced (a 10) 0 h59) (And.intro (forced (a 11) 0 h60) (And.intro (forced (a 12) 0 h66) (And.intro (forced (a 13) 0 h115) (And.intro (forced (a 14) 0 h41) (And.intro (forced (a 15) 0 h117) (And.intro (forced (a 16) 0 h130) (And.intro (forced (a 17) 0 h119) (And.intro (forced (a 18) 0 h122) (And.intro (forced (a 19) 0 h88) (And.intro (forced (a 20) 0 h96) (And.intro (forced (a 21) 0 h123) (And.intro (forced (a 22) 0 h97) (And.intro (forced (a 23) 0 h93) (And.intro (forced (a 24) 0 h99) (And.intro (forced (a 25) 0 h116) (And.intro (forced (a 26) 0 h124) (And.intro (forced (a 27) 0 h94) (And.intro (forced (a 28) 0 h125) (And.intro (forced (a 29) 0 h103) (And.intro (forced (a 30) 0 h104) (forced (a 31) 0 h101)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_216
