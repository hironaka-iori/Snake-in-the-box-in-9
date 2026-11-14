import PartitionData205_217
import PartitionPiece205_217_0
import PartitionPiece205_217_1
import PartitionPiece205_217_2
import PartitionPiece205_217_3
import PartitionPiece205_217_4
import PartitionPiece205_217_5
import PartitionPiece205_217_6
import PartitionPiece205_217_7
namespace PartitionCover205_217
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2])
    (start2 : a 2 ∈ [0,1,2,3])
    (start3 : a 3 ∈ [0,1,2,3,4])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
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
  have group1 := chunk0 a start2 start0 start4 start8 c1 c2 c3
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 start0 c3
  have h6 := group5
  have group7 := chunk2 a h6 start0 start16 c3 c4
  rcases group7 with ⟨h8,h9⟩
  have group10 := chunk3 a h9 start0 start5 start1 c4 c6
  rcases group10 with ⟨h11,h12⟩
  have group13 := chunk4 a h12 start1 start9 c6 c7
  rcases group13 with ⟨h14,h15⟩
  have group16 := chunk5 a h15 start1 start17 c7 c8
  rcases group16 with ⟨h17,h18⟩
  have group19 := chunk6 a h18 start1 start3 h2 start6 c8 c9 c10
  rcases group19 with ⟨h20,h21,h22⟩
  have group23 := chunk7 a h22 h2 c10
  have h24 := group23
  have group25 := chunk8 a h24 h2 start10 start18 c10 c11 c12
  rcases group25 with ⟨h26,h27,h28⟩
  have group29 := chunk9 a h28 h2 start7 h21 start11 c12 c13 c14
  rcases group29 with ⟨h30,h31,h32⟩
  have group33 := chunk10 a h32 h21 start19 h14 h3 h26 start12 c14 c15 c16 c17 c18
  rcases group33 with ⟨h34,h35,h36,h37,h38,h39⟩
  have group40 := chunk11 a h39 h37 c18
  have h41 := group40
  have group42 := chunk12 a start20 h37 c19
  have h43 := group42
  have group44 := chunk13 a h43 h37 h36 h31 start13 c19 c20 c21
  rcases group44 with ⟨h45,h46,h47,h48⟩
  have group49 := chunk14 a h48 h46 c21
  have h50 := group49
  have group51 := chunk15 a h50 h46 start21 c21 c22
  rcases group51 with ⟨h52,h53⟩
  have group54 := chunk16 a h53 h46 start14 h38 c22 c24
  rcases group54 with ⟨h55,h56⟩
  have group57 := chunk17 a h56 h38 c24
  have h58 := group57
  have group59 := chunk18 a start22 h38 c25
  have h60 := group59
  have group61 := chunk19 a h60 h38 start23 h47 c25 c27
  rcases group61 with ⟨h62,h63⟩
  have group64 := chunk20 a h17 h8 h27 h41 start24 c28 c29 c30 c31
  rcases group64 with ⟨h65,h66,h67,h68,h69⟩
  have group70 := chunk21 a h69 h66 h65 h34 c31 c32
  rcases group70 with ⟨h71,h72,h73⟩
  have group74 := chunk22 a h72 h52 start25 c33 c34
  rcases group74 with ⟨h75,h76⟩
  have group77 := chunk23 a h76 h75 h67 h73 start26 c34 c35 c37
  rcases group77 with ⟨h78,h79,h80⟩
  have group81 := chunk24 a h80 h79 start15 h73 start27 c37 c38 c39
  rcases group81 with ⟨h82,h83,h84⟩
  have group85 := chunk25 a h84 h73 h68 h52 h58 start28 c39 c40 c41 c42
  rcases group85 with ⟨h86,h87,h88,h89,h90⟩
  have group91 := chunk26 a h90 h87 h83 h88 start29 c42 c43 c44
  rcases group91 with ⟨h92,h93,h94⟩
  have group95 := chunk27 a h94 h88 start31 h93 c44 c47
  rcases group95 with ⟨h96,h97⟩
  have group98 := chunk28 a h97 h93 h20 h11 h30 h45 h35 c47 c48 c49 c50 c52
  rcases group98 with ⟨h99,h100,h101,h102,h103,h104⟩
  have group105 := chunk29 a h104 h100 h78 h102 h82 h55 h103 h62 h63 h99 h71 c52 c54 c55 c57 c60 c61 c63 c67 c68
  rcases group105 with ⟨h106,h107,h108,h109,h110,h111,h112,h113,h114⟩
  have group115 := chunk30 a h114 h78 h108 h86 start30 h92 h96 c68 c69 c71 c74 c76
  rcases group115 with ⟨h116,h117,h118,h119,h120⟩
  have group121 := chunk31 a h96 h120 h119 start1 h21 h46 h47 h37 h38 h89 h112 h106 h107 c5 c6 c13 c16 c20 c24 c27 c52 c58 c76 c77
  rcases group121 with ⟨h122,h123,h124,h125,h126,h127,h128,h129,h130,h131⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h124) (And.intro (forced (a 2) 0 h2) (And.intro (forced (a 3) 0 h125) (And.intro (forced (a 4) 0 h126) (And.intro (forced (a 5) 0 h130) (And.intro (forced (a 6) 0 h127) (And.intro (forced (a 7) 0 h128) (And.intro (forced (a 8) 0 h66) (And.intro (forced (a 9) 0 h75) (And.intro (forced (a 10) 0 h79) (And.intro (forced (a 11) 0 h73) (And.intro (forced (a 12) 0 h87) (And.intro (forced (a 13) 0 h88) (And.intro (forced (a 14) 0 h89) (And.intro (forced (a 15) 0 h93) (And.intro (forced (a 16) 0 h101) (And.intro (forced (a 17) 0 h131) (And.intro (forced (a 18) 0 h102) (And.intro (forced (a 19) 0 h129) (And.intro (forced (a 20) 0 h110) (And.intro (forced (a 21) 0 h109) (And.intro (forced (a 22) 0 h111) (And.intro (forced (a 23) 0 h112) (And.intro (forced (a 24) 0 h116) (And.intro (forced (a 25) 0 h117) (And.intro (forced (a 26) 0 h108) (And.intro (forced (a 27) 0 h118) (And.intro (forced (a 28) 0 h120) (And.intro (forced (a 29) 0 h122) (And.intro (forced (a 30) 0 h123) (forced (a 31) 0 h113)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_217
