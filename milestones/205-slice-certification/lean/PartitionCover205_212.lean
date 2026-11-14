import PartitionData205_212
import PartitionPiece205_212_0
import PartitionPiece205_212_1
import PartitionPiece205_212_2
import PartitionPiece205_212_3
import PartitionPiece205_212_4
import PartitionPiece205_212_5
import PartitionPiece205_212_6
namespace PartitionCover205_212
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start7 : a 7 ∈ [0,1,2])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
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
  have group1 := chunk0 a start2 start0 c1
  have h2 := group1
  have group3 := chunk1 a h2 start0 start4 start8 c1 c2 c3
  rcases group3 with ⟨h4,h5,h6⟩
  have group7 := chunk2 a h6 start0 start16 c3 c4
  rcases group7 with ⟨h8,h9⟩
  have group10 := chunk3 a h9 start0 start9 start1 c4 c7
  rcases group10 with ⟨h11,h12⟩
  have group13 := chunk4 a h12 start1 start17 start6 h4 c7 c8 c10
  rcases group13 with ⟨h14,h15,h16⟩
  have group17 := chunk5 a h16 h4 start10 c10 c11
  rcases group17 with ⟨h18,h19⟩
  have group20 := chunk6 a h19 h4 start18 c11 c12
  rcases group20 with ⟨h21,h22⟩
  have group23 := chunk7 a h22 h4 start11 start3 c12 c14
  rcases group23 with ⟨h24,h25⟩
  have group26 := chunk8 a h25 start3 start19 c14 c15
  rcases group26 with ⟨h27,h28⟩
  have group29 := chunk9 a h28 start3 start12 h5 start20 start13 start5 c15 c18 c19 c21
  rcases group29 with ⟨h30,h31,h32,h33⟩
  have group34 := chunk10 a h33 start5 start14 h18 start22 start23 start7 h8 h14 h31 c21 c24 c25 c27 c28 c30
  rcases group34 with ⟨h35,h36,h37,h38,h39,h40⟩
  have group41 := chunk11 a h40 h39 start24 c30 c31
  rcases group41 with ⟨h42,h43⟩
  have group44 := chunk12 a h43 h39 h27 h14 h35 start25 c31 c32 c33 c34
  rcases group44 with ⟨h45,h46,h47,h48⟩
  have group49 := chunk13 a h48 h14 h36 h21 c34 c36
  rcases group49 with ⟨h50,h51⟩
  have group52 := chunk14 a h51 h21 start26 start15 h46 c36 c37 c38
  rcases group52 with ⟨h53,h54,h55⟩
  have group56 := chunk15 a h55 h46 start27 c38 c39
  rcases group56 with ⟨h57,h58⟩
  have group59 := chunk16 a h58 h46 start28 h42 c39 c42
  rcases group59 with ⟨h60,h61⟩
  have group62 := chunk17 a h61 h42 start29 h47 c42 c44
  rcases group62 with ⟨h63,h64⟩
  have group65 := chunk18 a h64 h47 h53 h57 start30 c44 c45 c46
  rcases group65 with ⟨h66,h67,h68⟩
  have group69 := chunk19 a h68 h67 h11 h32 h45 start21 h15 c46 c50 c51 c53
  rcases group69 with ⟨h70,h71,h72,h73⟩
  have group74 := chunk20 a h73 h15 h50 h37 h24 h30 h38 c53 c54 c56 c58
  rcases group74 with ⟨h75,h76,h77,h78,h79⟩
  have group80 := chunk21 a h79 h78 h75 h72 h66 h77 start31 c58 c60 c63 c64 c65 c67
  rcases group80 with ⟨h81,h82,h83,h84,h85⟩
  have group86 := chunk22 a h85 h81 h54 h45 h63 c67 c69 c70
  rcases group86 with ⟨h87,h88,h89,h90⟩
  have group91 := chunk23 a h60 h76 h83 h87 h70 h90 h5 h42 start5 h82 h18 h67 c18 c22 c24 c71 c72 c75 c77 c78
  rcases group91 with ⟨h92,h93,h94,h95,h96,h97,h98⟩
  have group99 := chunk24 a start7 h57 h21 h67 h24 h71 h72 h15 h82 h78 h84 h88 h92 start1 h97 h4 h98 start3 c6 c10 c12 c15 c26 c36 c49 c50 c53 c55 c56 c57 c59
  rcases group99 with ⟨h100,h101,h102,h103,h104,h105,h106,h107,h108,h109,h110⟩
  have group111 := chunk25 a h100 h97 h57 h101 h106 h46 h98 h109 h14 c10 c20 c26 c32 c37 c38
  rcases group111 with ⟨h112,h113,h114,h115,h116,h117⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h108) (And.intro (forced (a 2) 0 h109) (And.intro (forced (a 3) 0 h110) (And.intro (forced (a 4) 0 h96) (And.intro (forced (a 5) 0 h97) (And.intro (forced (a 6) 0 h116) (And.intro (forced (a 7) 0 h112) (And.intro (forced (a 8) 0 h39) (And.intro (forced (a 9) 0 h117) (And.intro (forced (a 10) 0 h114) (And.intro (forced (a 11) 0 h115) (And.intro (forced (a 12) 0 h42) (And.intro (forced (a 13) 0 h47) (And.intro (forced (a 14) 0 h67) (And.intro (forced (a 15) 0 h113) (And.intro (forced (a 16) 0 h71) (And.intro (forced (a 17) 0 h104) (And.intro (forced (a 18) 0 h102) (And.intro (forced (a 19) 0 h105) (And.intro (forced (a 20) 0 h103) (And.intro (forced (a 21) 0 h82) (And.intro (forced (a 22) 0 h84) (And.intro (forced (a 23) 0 h81) (And.intro (forced (a 24) 0 h89) (And.intro (forced (a 25) 0 h93) (And.intro (forced (a 26) 0 h106) (And.intro (forced (a 27) 0 h107) (And.intro (forced (a 28) 0 h90) (And.intro (forced (a 29) 0 h83) (And.intro (forced (a 30) 0 h95) (forced (a 31) 0 h94)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_212
