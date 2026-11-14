import PartitionData205_208
import PartitionPiece205_208_0
import PartitionPiece205_208_1
import PartitionPiece205_208_2
import PartitionPiece205_208_3
import PartitionPiece205_208_4
namespace PartitionCover205_208
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3])
    (start3 : a 3 ∈ [0,1,2,3])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0,1,2,3])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start16 : a 16 ∈ [0,1,2,3,4,5])
    (start17 : a 17 ∈ [0,1,2,3,4,5])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start19 : a 19 ∈ [0,1,2,3,4,5])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start22 : a 22 ∈ [0,1,2,3])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=2 ∧ a 3=2 ∧ a 4=1 ∧ a 5=3 ∧ a 6=2 ∧ a 7=4 ∧ a 8=6 ∧ a 9=8 ∧ a 10=0 ∧ a 11=8 ∧ a 12=6 ∧ a 13=1 ∧ a 14=0 ∧ a 15=8 ∧ a 16=3 ∧ a 17=3 ∧ a 18=0 ∧ a 19=3 ∧ a 20=6 ∧ a 21=6 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=12 ∧ a 26=9 ∧ a 27=12 ∧ a 28=0 ∧ a 29=12 ∧ a 30=1 ∧ a 31=6) := by
  have group1 := chunk0 a start2 start0 start8 start16 start5 start1 start9 c1 c3 c4 c6 c7
  rcases group1 with ⟨h2,h3,h4,h5,h6⟩
  have group7 := chunk1 a h6 start1 start17 start3 h2 start6 start10 c7 c8 c9 c10 c11
  rcases group7 with ⟨h8,h9,h10,h11,h12⟩
  have group13 := chunk2 a h12 h2 start18 start7 h10 c11 c12 c13
  rcases group13 with ⟨h14,h15,h16⟩
  have group17 := chunk3 a h16 h10 start19 start12 start4 h5 start13 c13 c15 c18 c20 c21
  rcases group17 with ⟨h18,h19,h20,h21,h22⟩
  have group23 := chunk4 a h22 h21 start21 start22 h11 c21 c22 c25
  rcases group23 with ⟨h24,h25,h26⟩
  have group27 := chunk5 a start15 h18 start23 h8 h3 start24 c26 c27 c28 c31
  rcases group27 with ⟨h28,h29,h30,h31⟩
  have group32 := chunk6 a h31 h3 start11 h30 c31 c32
  rcases group32 with ⟨h33,h34⟩
  have group35 := chunk7 a h34 h30 h14 start14 start26 c32 c35 c36 c37
  rcases group35 with ⟨h36,h37,h38,h39⟩
  have group40 := chunk8 a h39 h37 h28 h36 h24 h20 start28 c37 c38 c40 c42
  rcases group40 with ⟨h41,h42,h43,h44⟩
  have group45 := chunk9 a h44 h20 start29 h43 c42 c44
  rcases group45 with ⟨h46,h47⟩
  have group48 := chunk10 a h47 h43 start30 h38 c44 c46
  rcases group48 with ⟨h49,h50⟩
  have group51 := chunk11 a start31 h42 h9 h4 start20 c47 c48 c50
  rcases group51 with ⟨h52,h53,h54⟩
  have group55 := chunk12 a h54 h4 h25 h53 h15 h19 h26 h29 start27 c50 c53 c55 c56 c58 c59
  rcases group55 with ⟨h56,h57,h58,h59,h60,h61⟩
  have group62 := chunk13 a h61 h19 h56 h57 h49 h60 h59 start25 h33 c59 c60 c64 c65 c68
  rcases group62 with ⟨h63,h64,h65,h66,h67⟩
  have group68 := chunk14 a h67 h33 h46 c68 c70
  rcases group68 with ⟨h69,h70⟩
  have group71 := chunk15 a h46 h70 h69 h63 h18 h42 c26 c70 c71
  rcases group71 with ⟨h72,h73,h74,h75⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q76 | q77
  · have h78 : a 1 ∈ [0] := List.mem_singleton.mpr q76
    have group79 := chunk16 a h10 h78 h2 h11 h75 start4 h20 h64 h21 h57 h42 h3 h36 h43 h65 h52 h4 c5 c9 c10 c13 c17 c18 c19 c20 c22 c26 c30 c38 c40 c44 c47 c50
    rcases group79 with ⟨h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91,h92,h93,h94,h95⟩
    have group96 := chunk17 a h53 h88 h73 h93 h50 h94 h30 h90 h19 h74 h41 c28 c52 c53 c71 c72 c73 c79
    rcases group96 with ⟨h97,h98,h99,h100,h101,h102,h103⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h78) (And.intro (forced (a 2) 0 h81) (And.intro (forced (a 3) 0 h80) (And.intro (forced (a 4) 0 h84) (And.intro (forced (a 5) 0 h87) (And.intro (forced (a 6) 0 h82) (And.intro (forced (a 7) 0 h83) (And.intro (forced (a 8) 0 h90) (And.intro (forced (a 9) 0 h100) (And.intro (forced (a 10) 0 h37) (And.intro (forced (a 11) 0 h91) (And.intro (forced (a 12) 0 h85) (And.intro (forced (a 13) 0 h92) (And.intro (forced (a 14) 0 h38) (And.intro (forced (a 15) 0 h89) (And.intro (forced (a 16) 0 h95) (And.intro (forced (a 17) 0 h97) (And.intro (forced (a 18) 0 h58) (And.intro (forced (a 19) 0 h101) (And.intro (forced (a 20) 0 h86) (And.intro (forced (a 21) 0 h88) (And.intro (forced (a 22) 0 h59) (And.intro (forced (a 23) 0 h66) (And.intro (forced (a 24) 0 h70) (And.intro (forced (a 25) 0 h98) (And.intro (forced (a 26) 0 h103) (And.intro (forced (a 27) 0 h102) (And.intro (forced (a 28) 0 h72) (And.intro (forced (a 29) 0 h93) (And.intro (forced (a 30) 0 h99) (forced (a 31) 0 h94))))))))))))))))))))))))))))))))
  · have h104 : a 1 ∈ [1] := List.mem_singleton.mpr q77
    have group105 := chunk18 a h10 h104 h2 h11 h75 start4 h20 h64 h21 h57 h42 h3 h36 h43 h65 h52 h4 c5 c9 c10 c13 c17 c18 c19 c20 c22 c26 c30 c38 c40 c44 c47 c50
    rcases group105 with ⟨h106,h107,h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119,h120,h121⟩
    have group122 := chunk19 a h53 h114 h73 h119 h50 h120 h30 h116 h19 h74 h41 c28 c52 c53 c71 c72 c73 c79
    rcases group122 with ⟨h123,h124,h125,h126,h127,h128,h129⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h104) (And.intro (forced (a 2) 2 h107) (And.intro (forced (a 3) 2 h106) (And.intro (forced (a 4) 1 h110) (And.intro (forced (a 5) 3 h113) (And.intro (forced (a 6) 2 h108) (And.intro (forced (a 7) 4 h109) (And.intro (forced (a 8) 6 h116) (And.intro (forced (a 9) 8 h126) (And.intro (forced (a 10) 0 h37) (And.intro (forced (a 11) 8 h117) (And.intro (forced (a 12) 6 h111) (And.intro (forced (a 13) 1 h118) (And.intro (forced (a 14) 0 h38) (And.intro (forced (a 15) 8 h115) (And.intro (forced (a 16) 3 h121) (And.intro (forced (a 17) 3 h123) (And.intro (forced (a 18) 0 h58) (And.intro (forced (a 19) 3 h127) (And.intro (forced (a 20) 6 h112) (And.intro (forced (a 21) 6 h114) (And.intro (forced (a 22) 0 h59) (And.intro (forced (a 23) 0 h66) (And.intro (forced (a 24) 0 h70) (And.intro (forced (a 25) 12 h124) (And.intro (forced (a 26) 9 h129) (And.intro (forced (a 27) 12 h128) (And.intro (forced (a 28) 0 h72) (And.intro (forced (a 29) 12 h119) (And.intro (forced (a 30) 1 h125) (forced (a 31) 6 h120))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_208
