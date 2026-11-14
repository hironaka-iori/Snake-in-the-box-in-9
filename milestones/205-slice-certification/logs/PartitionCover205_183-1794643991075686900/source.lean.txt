import PartitionData205_183
import PartitionPiece205_183_0
import PartitionPiece205_183_1
import PartitionPiece205_183_2
import PartitionPiece205_183_3
import PartitionPiece205_183_4
namespace PartitionCover205_183
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1,2,3,4,5])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start7 : a 7 ∈ [0,1,2])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2])
    (start10 : a 10 ∈ [0,1,2])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start28 : a 28 ∈ [0,1,2,3])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start30 : a 30 ∈ [0,1,2,3,4,5])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 15)=true)
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 16)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 17)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 18)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 19)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 20)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 21)=true)
    (c26 : edge r26 (a 7) (a 22)=true)
    (c27 : edge r27 (a 8) (a 9)=true)
    (c28 : edge r28 (a 8) (a 10)=true)
    (c29 : edge r29 (a 8) (a 12)=true)
    (c30 : edge r30 (a 8) (a 23)=true)
    (c31 : edge r31 (a 9) (a 11)=true)
    (c32 : edge r32 (a 9) (a 13)=true)
    (c33 : edge r33 (a 9) (a 24)=true)
    (c34 : edge r34 (a 10) (a 11)=true)
    (c35 : edge r35 (a 10) (a 14)=true)
    (c36 : edge r36 (a 10) (a 25)=true)
    (c37 : edge r37 (a 11) (a 26)=true)
    (c38 : edge r38 (a 12) (a 13)=true)
    (c39 : edge r39 (a 12) (a 14)=true)
    (c40 : edge r40 (a 12) (a 27)=true)
    (c41 : edge r41 (a 13) (a 28)=true)
    (c42 : edge r42 (a 14) (a 29)=true)
    (c43 : edge r43 (a 15) (a 16)=true)
    (c44 : edge r44 (a 15) (a 17)=true)
    (c45 : edge r45 (a 15) (a 19)=true)
    (c46 : edge r46 (a 15) (a 23)=true)
    (c47 : edge r47 (a 16) (a 18)=true)
    (c48 : edge r48 (a 16) (a 20)=true)
    (c49 : edge r49 (a 16) (a 24)=true)
    (c50 : edge r50 (a 17) (a 18)=true)
    (c51 : edge r51 (a 17) (a 21)=true)
    (c52 : edge r52 (a 17) (a 25)=true)
    (c53 : edge r53 (a 18) (a 22)=true)
    (c54 : edge r54 (a 18) (a 26)=true)
    (c55 : edge r55 (a 19) (a 20)=true)
    (c56 : edge r56 (a 19) (a 21)=true)
    (c57 : edge r57 (a 19) (a 27)=true)
    (c58 : edge r58 (a 20) (a 22)=true)
    (c59 : edge r59 (a 20) (a 28)=true)
    (c60 : edge r60 (a 21) (a 22)=true)
    (c61 : edge r61 (a 21) (a 29)=true)
    (c62 : edge r62 (a 22) (a 30)=true)
    (c63 : edge r63 (a 23) (a 24)=true)
    (c64 : edge r64 (a 23) (a 25)=true)
    (c65 : edge r65 (a 23) (a 27)=true)
    (c66 : edge r66 (a 24) (a 26)=true)
    (c67 : edge r67 (a 24) (a 28)=true)
    (c68 : edge r68 (a 25) (a 26)=true)
    (c69 : edge r69 (a 25) (a 29)=true)
    (c70 : edge r70 (a 26) (a 30)=true)
    (c71 : edge r71 (a 27) (a 28)=true)
    (c72 : edge r72 (a 27) (a 29)=true)
    (c73 : edge r73 (a 28) (a 30)=true)
    (c74 : edge r74 (a 29) (a 30)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0) ∨
      (a 0=0 ∧ a 1=0 ∧ a 2=1 ∧ a 3=1 ∧ a 4=3 ∧ a 5=3 ∧ a 6=2 ∧ a 7=0 ∧ a 8=1 ∧ a 9=1 ∧ a 10=1 ∧ a 11=1 ∧ a 12=1 ∧ a 13=12 ∧ a 14=2 ∧ a 15=3 ∧ a 16=6 ∧ a 17=0 ∧ a 18=2 ∧ a 19=6 ∧ a 20=0 ∧ a 21=1 ∧ a 22=2 ∧ a 23=0 ∧ a 24=6 ∧ a 25=3 ∧ a 26=2 ∧ a 27=6 ∧ a 28=0 ∧ a 29=1 ∧ a 30=2) := by
  have group1 := chunk0 a start2 start0 start4 start15 c1 c2 c4
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 start0 start5 start1 start16 c4 c6 c8
  rcases group5 with ⟨h6,h7,h8⟩
  have group9 := chunk2 a h8 start1 start3 h2 start6 c8 c9 c10
  rcases group9 with ⟨h10,h11,h12⟩
  have group13 := chunk3 a h12 h2 start10 start17 start7 h11 start11 c10 c11 c12 c13 c14
  rcases group13 with ⟨h14,h15,h16,h17,h18⟩
  have group19 := chunk4 a h18 h11 h3 h7 start12 start19 c14 c16 c18 c19
  rcases group19 with ⟨h20,h21,h22,h23,h24⟩
  have group25 := chunk5 a h24 h21 start13 h22 c19 c21
  rcases group25 with ⟨h26,h27⟩
  have group28 := chunk6 a h27 h22 start20 h14 h17 start14 c21 c22 c23 c24
  rcases group28 with ⟨h29,h30,h31,h32⟩
  have group33 := chunk7 a h32 h31 start22 h17 start9 start8 c24 c26 c27
  rcases group33 with ⟨h34,h35,h36⟩
  have group37 := chunk8 a start8 h15 start23 h29 h36 start24 start25 c28 c30 c32 c33 c36
  rcases group37 with ⟨h38,h39,h40,h41,h42⟩
  have group43 := chunk9 a h42 h15 start26 h20 h23 h40 h34 start27 c36 c37 c38 c39 c40
  rcases group43 with ⟨h44,h45,h46,h47⟩
  have group48 := chunk10 a h47 h46 start29 h34 h10 h6 c40 c42 c43
  rcases group48 with ⟨h49,h50,h51⟩
  have group52 := chunk11 a h51 h6 h26 h39 h30 h41 c43 c45 c46 c48 c49
  rcases group52 with ⟨h53,h54,h55,h56,h57⟩
  have group58 := chunk12 a h57 h53 start18 h16 c49 c50
  rcases group58 with ⟨h59,h60⟩
  have group61 := chunk13 a h60 h16 start21 c50 c51
  rcases group61 with ⟨h62,h63⟩
  have group64 := chunk14 a h63 h16 h44 h45 h62 h54 h56 h49 start28 c51 c52 c54 c55 c57 c59
  rcases group64 with ⟨h65,h66,h67,h68,h69,h70⟩
  have group71 := chunk15 a h70 h56 h50 h65 start30 h35 h40 c41 c59 c61 c62
  rcases group71 with ⟨h72,h73,h74,h75⟩
  rcases (show a 2=0 ∨ a 2=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h2) with q76 | q77
  · have h78 : a 2 ∈ [0] := List.mem_singleton.mpr q76
    have group79 := chunk16 a h11 h78 h31 h15 h20 h21 h46 h68 h34 h38 h36 h75 h59 h66 h67 h6 h53 c9 c10 c11 c14 c17 c18 c19 c24 c28 c31 c32 c33 c36 c37 c45 c49
    rcases group79 with ⟨h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91,h92,h93,h94,h95⟩
    have group96 := chunk17 a h62 h93 h69 h86 h73 h92 h74 h22 h84 h35 h65 c16 c53 c54 c57 c60 c69 c70
    rcases group96 with ⟨h97,h98,h99,h100,h101,h102,h103⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h78) (And.intro (forced (a 3) 0 h80) (And.intro (forced (a 4) 0 h84) (And.intro (forced (a 5) 0 h101) (And.intro (forced (a 6) 0 h81) (And.intro (forced (a 7) 0 h17) (And.intro (forced (a 8) 0 h88) (And.intro (forced (a 9) 0 h89) (And.intro (forced (a 10) 0 h82) (And.intro (forced (a 11) 0 h83) (And.intro (forced (a 12) 0 h85) (And.intro (forced (a 13) 0 h90) (And.intro (forced (a 14) 0 h87) (And.intro (forced (a 15) 0 h94) (And.intro (forced (a 16) 0 h95) (And.intro (forced (a 17) 0 h16) (And.intro (forced (a 18) 0 h97) (And.intro (forced (a 19) 0 h86) (And.intro (forced (a 20) 0 h56) (And.intro (forced (a 21) 0 h103) (And.intro (forced (a 22) 0 h102) (And.intro (forced (a 23) 0 h55) (And.intro (forced (a 24) 0 h91) (And.intro (forced (a 25) 0 h92) (And.intro (forced (a 26) 0 h93) (And.intro (forced (a 27) 0 h98) (And.intro (forced (a 28) 0 h72) (And.intro (forced (a 29) 0 h99) (forced (a 30) 0 h100)))))))))))))))))))))))))))))))
  · have h104 : a 2 ∈ [1] := List.mem_singleton.mpr q77
    have group105 := chunk18 a h11 h104 h31 h15 h20 h21 h46 h68 h34 h38 h36 h75 h59 h66 h67 h6 h53 c9 c10 c11 c14 c17 c18 c19 c24 c28 c31 c32 c33 c36 c37 c45 c49
    rcases group105 with ⟨h106,h107,h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119,h120,h121⟩
    have group122 := chunk19 a h62 h119 h69 h112 h73 h118 h74 h22 h110 h35 h65 c16 c53 c54 c57 c60 c69 c70
    rcases group122 with ⟨h123,h124,h125,h126,h127,h128,h129⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 1 h104) (And.intro (forced (a 3) 1 h106) (And.intro (forced (a 4) 3 h110) (And.intro (forced (a 5) 3 h127) (And.intro (forced (a 6) 2 h107) (And.intro (forced (a 7) 0 h17) (And.intro (forced (a 8) 1 h114) (And.intro (forced (a 9) 1 h115) (And.intro (forced (a 10) 1 h108) (And.intro (forced (a 11) 1 h109) (And.intro (forced (a 12) 1 h111) (And.intro (forced (a 13) 12 h116) (And.intro (forced (a 14) 2 h113) (And.intro (forced (a 15) 3 h120) (And.intro (forced (a 16) 6 h121) (And.intro (forced (a 17) 0 h16) (And.intro (forced (a 18) 2 h123) (And.intro (forced (a 19) 6 h112) (And.intro (forced (a 20) 0 h56) (And.intro (forced (a 21) 1 h129) (And.intro (forced (a 22) 2 h128) (And.intro (forced (a 23) 0 h55) (And.intro (forced (a 24) 6 h117) (And.intro (forced (a 25) 3 h118) (And.intro (forced (a 26) 2 h119) (And.intro (forced (a 27) 6 h124) (And.intro (forced (a 28) 0 h72) (And.intro (forced (a 29) 1 h125) (forced (a 30) 2 h126)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_183
