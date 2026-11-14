import PartitionData205_213
import PartitionPiece205_213_0
import PartitionPiece205_213_1
import PartitionPiece205_213_2
import PartitionPiece205_213_3
import PartitionPiece205_213_4
import PartitionPiece205_213_5
namespace PartitionCover205_213
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start5 : a 5 ∈ [0,1,2,3])
    (start6 : a 6 ∈ [0,1,2])
    (start7 : a 7 ∈ [0,1,2])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start15 : a 15 ∈ [0,1,2,3,4,5])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start19 : a 19 ∈ [0,1,2,3,4,5])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start23 : a 23 ∈ [0,1,2])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
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
  have group1 := chunk0 a start2 start0 start4 start8 c1 c2 c3
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 start0 c3
  have h6 := group5
  have group7 := chunk2 a h6 start0 start16 c3 c4
  rcases group7 with ⟨h8,h9⟩
  have group10 := chunk3 a h9 start0 start9 start1 start17 c4 c7 c8
  rcases group10 with ⟨h11,h12,h13⟩
  have group14 := chunk4 a h13 start1 h2 start3 start6 start10 c8 c9 c10 c11
  rcases group14 with ⟨h15,h16,h17,h18⟩
  have group19 := chunk5 a h18 h16 start18 c11 c12
  rcases group19 with ⟨h20,h21⟩
  have group22 := chunk6 a h21 h16 start11 start3 c12 c14
  rcases group22 with ⟨h23,h24⟩
  have group25 := chunk7 a h24 start3 start19 start5 h3 h17 start12 c14 c15 c16 c17 c18
  rcases group25 with ⟨h26,h27,h28,h29,h30⟩
  have group31 := chunk8 a h30 h29 start20 h28 start7 start13 c18 c19 c20 c21
  rcases group31 with ⟨h32,h33,h34,h35,h36⟩
  have group37 := chunk9 a h36 h34 start21 h35 h17 start22 c21 c22 c23 c25
  rcases group37 with ⟨h38,h39,h40,h41⟩
  have group42 := chunk10 a h41 h17 start15 h40 start23 h8 h12 h32 start24 c25 c26 c27 c28 c30 c31
  rcases group42 with ⟨h43,h44,h45,h46,h47⟩
  have group48 := chunk11 a h47 h46 start25 h12 c31 c34
  rcases group48 with ⟨h49,h50⟩
  have group51 := chunk12 a h50 h12 start14 h20 c34 c36
  rcases group51 with ⟨h52,h53⟩
  have group54 := chunk13 a h53 h20 start26 h26 h44 start27 c36 c37 c38 c39
  rcases group54 with ⟨h55,h56,h57,h58,h59⟩
  have group60 := chunk14 a h59 h57 c39
  have h61 := group60
  have group62 := chunk15 a h32 h38 h55 start28 c40 c41 c42
  rcases group62 with ⟨h63,h64,h65⟩
  have group66 := chunk16 a h65 h63 start29 h38 start30 h64 c42 c44 c46
  rcases group66 with ⟨h67,h68,h69⟩
  have group70 := chunk17 a h69 h64 h11 h33 h49 c46 c50 c51
  rcases group70 with ⟨h71,h72,h73⟩
  have group74 := chunk18 a h15 h39 h52 h45 h27 h61 h73 h43 h67 h68 h71 h56 h49 c53 c54 c58 c59 c60 c61 c62 c64 c66 c69
  rcases group74 with ⟨h75,h76,h77,h78,h79,h80,h81,h82,h83,h84⟩
  have group85 := chunk19 a h84 h49 h82 h77 h61 start31 c69 c70 c71 c73 c75
  rcases group85 with ⟨h86,h87,h88,h89⟩
  have group90 := chunk20 a h89 h61 start1 h34 start3 h40 h20 h46 h12 h57 h23 h72 h81 h16 c6 c9 c13 c29 c32 c49 c56 c75
  rcases group90 with ⟨h91,h92,h93,h94,h95,h96,h97,h98⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h92) (And.intro (forced (a 2) 0 h98) (And.intro (forced (a 3) 0 h93) (And.intro (forced (a 4) 0 h29) (And.intro (forced (a 5) 0 h34) (And.intro (forced (a 6) 0 h17) (And.intro (forced (a 7) 0 h40) (And.intro (forced (a 8) 0 h46) (And.intro (forced (a 9) 0 h95) (And.intro (forced (a 10) 0 h94) (And.intro (forced (a 11) 0 h57) (And.intro (forced (a 12) 0 h63) (And.intro (forced (a 13) 0 h38) (And.intro (forced (a 14) 0 h64) (And.intro (forced (a 15) 0 h58) (And.intro (forced (a 16) 0 h72) (And.intro (forced (a 17) 0 h75) (And.intro (forced (a 18) 0 h96) (And.intro (forced (a 19) 0 h79) (And.intro (forced (a 20) 0 h80) (And.intro (forced (a 21) 0 h76) (And.intro (forced (a 22) 0 h97) (And.intro (forced (a 23) 0 h78) (And.intro (forced (a 24) 0 h87) (And.intro (forced (a 25) 0 h88) (And.intro (forced (a 26) 0 h86) (And.intro (forced (a 27) 0 h61) (And.intro (forced (a 28) 0 h82) (And.intro (forced (a 29) 0 h83) (And.intro (forced (a 30) 0 h71) (forced (a 31) 0 h91)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_213
