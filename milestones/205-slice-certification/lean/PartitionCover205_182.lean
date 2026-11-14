import PartitionData205_182
import PartitionPiece205_182_0
import PartitionPiece205_182_1
import PartitionPiece205_182_2
import PartitionPiece205_182_3
import PartitionPiece205_182_4
namespace PartitionCover205_182
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1,2,3,4,5])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1,2,3])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start7 : a 7 ∈ [0,1,2])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start9 : a 9 ∈ [0,1,2])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (start14 : a 14 ∈ [0,1,2,3,4,5])
    (start15 : a 15 ∈ [0,1,2,3,4,5])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8])
    (start19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7,8])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7,8])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
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
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0) ∨
      (a 0=0 ∧ a 1=0 ∧ a 2=1 ∧ a 3=1 ∧ a 4=1 ∧ a 5=1 ∧ a 6=2 ∧ a 7=0 ∧ a 8=6 ∧ a 9=0 ∧ a 10=2 ∧ a 11=2 ∧ a 12=1 ∧ a 13=3 ∧ a 14=0 ∧ a 15=1 ∧ a 16=1 ∧ a 17=1 ∧ a 18=0 ∧ a 19=1 ∧ a 20=1 ∧ a 21=0 ∧ a 22=2 ∧ a 23=1 ∧ a 24=4 ∧ a 25=1 ∧ a 26=1 ∧ a 27=1 ∧ a 28=1 ∧ a 29=6 ∧ a 30=2 ∧ a 31=0) := by
  have group1 := chunk0 a start2 start0 start8 start16 c1 c3 c4
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 start0 start5 start1 start17 c4 c6 c8
  rcases group5 with ⟨h6,h7,h8⟩
  have group9 := chunk2 a h8 start1 start3 h2 start6 c8 c9 c10
  rcases group9 with ⟨h10,h11,h12⟩
  have group13 := chunk3 a h12 h2 start10 start18 c10 c11 c12
  rcases group13 with ⟨h14,h15,h16⟩
  have group17 := chunk4 a h16 h2 start7 h11 start11 start4 h7 start20 c12 c13 c14 c16 c19
  rcases group17 with ⟨h18,h19,h20,h21,h22⟩
  have group23 := chunk5 a start13 h7 start21 h14 h19 start14 c21 c22 c23 c24
  rcases group23 with ⟨h24,h25,h26,h27⟩
  have group28 := chunk6 a h27 h26 start15 h19 start23 c24 c26 c27
  rcases group28 with ⟨h29,h30,h31⟩
  have group32 := chunk7 a h15 h3 start24 start9 h20 h24 c29 c31 c32 c33
  rcases group32 with ⟨h33,h34,h35,h36,h37⟩
  have group38 := chunk8 a h37 h35 start25 start26 h33 start27 h36 c33 c34 c37 c39
  rcases group38 with ⟨h39,h40,h41,h42⟩
  have group43 := chunk9 a h42 h36 start28 start12 c39 c42
  rcases group43 with ⟨h44,h45⟩
  have group46 := chunk10 a h45 start12 start29 h39 start30 h29 c42 c44 c46
  rcases group46 with ⟨h47,h48,h49⟩
  have group50 := chunk11 a h49 h29 h10 h6 h22 h34 h40 c46 c48 c50 c51 c54
  rcases group50 with ⟨h51,h52,h53,h54,h55⟩
  have group56 := chunk12 a start19 h18 c55
  have h57 := group56
  have group58 := chunk13 a start22 h18 c56
  have h59 := group58
  have group60 := chunk14 a h41 h18 h47 h53 h48 h25 h51 h59 c57 c62 c64 c66
  rcases group60 with ⟨h61,h62,h63,h64⟩
  have group65 := chunk15 a h64 h59 start31 h31 h44 h39 h63 c44 c66 c67 c75
  rcases group65 with ⟨h66,h67,h68⟩
  rcases (show a 2=0 ∨ a 2=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h2) with q69 | q70
  · have h71 : a 2 ∈ [0] := List.mem_singleton.mpr q69
    have group72 := chunk16 a h11 h71 h26 h33 h36 h21 start12 h53 h3 h54 h68 h62 h30 h63 h6 h66 h7 c9 c10 c11 c14 c16 c17 c18 c19 c29 c31 c40 c42 c43 c44 c50 c77
    rcases group72 with ⟨h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87,h88⟩
    have group89 := chunk17 a h52 h86 h55 h59 h87 h61 h31 h57 h44 c48 c54 c58 c59 c65 c66 c74
    rcases group89 with ⟨h90,h91,h92,h93,h94,h95,h96⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h71) (And.intro (forced (a 3) 0 h73) (And.intro (forced (a 4) 0 h77) (And.intro (forced (a 5) 0 h88) (And.intro (forced (a 6) 0 h74) (And.intro (forced (a 7) 0 h19) (And.intro (forced (a 8) 0 h80) (And.intro (forced (a 9) 0 h35) (And.intro (forced (a 10) 0 h75) (And.intro (forced (a 11) 0 h76) (And.intro (forced (a 12) 0 h78) (And.intro (forced (a 13) 0 h82) (And.intro (forced (a 14) 0 h29) (And.intro (forced (a 15) 0 h84) (And.intro (forced (a 16) 0 h86) (And.intro (forced (a 17) 0 h90) (And.intro (forced (a 18) 0 h18) (And.intro (forced (a 19) 0 h95) (And.intro (forced (a 20) 0 h79) (And.intro (forced (a 21) 0 h25) (And.intro (forced (a 22) 0 h92) (And.intro (forced (a 23) 0 h94) (And.intro (forced (a 24) 0 h81) (And.intro (forced (a 25) 0 h91) (And.intro (forced (a 26) 0 h93) (And.intro (forced (a 27) 0 h96) (And.intro (forced (a 28) 0 h83) (And.intro (forced (a 29) 0 h85) (And.intro (forced (a 30) 0 h87) (forced (a 31) 0 h67))))))))))))))))))))))))))))))))
  · have h97 : a 2 ∈ [1] := List.mem_singleton.mpr q70
    have group98 := chunk18 a h11 h97 h26 h33 h36 h21 start12 h53 h3 h54 h68 h62 h30 h63 h6 h66 h7 c9 c10 c11 c14 c16 c17 c18 c19 c29 c31 c40 c42 c43 c44 c50 c77
    rcases group98 with ⟨h99,h100,h101,h102,h103,h104,h105,h106,h107,h108,h109,h110,h111,h112,h113,h114⟩
    have group115 := chunk19 a h52 h112 h55 h59 h113 h61 h31 h57 h44 c48 c54 c58 c59 c65 c66 c74
    rcases group115 with ⟨h116,h117,h118,h119,h120,h121,h122⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 1 h97) (And.intro (forced (a 3) 1 h99) (And.intro (forced (a 4) 1 h103) (And.intro (forced (a 5) 1 h114) (And.intro (forced (a 6) 2 h100) (And.intro (forced (a 7) 0 h19) (And.intro (forced (a 8) 6 h106) (And.intro (forced (a 9) 0 h35) (And.intro (forced (a 10) 2 h101) (And.intro (forced (a 11) 2 h102) (And.intro (forced (a 12) 1 h104) (And.intro (forced (a 13) 3 h108) (And.intro (forced (a 14) 0 h29) (And.intro (forced (a 15) 1 h110) (And.intro (forced (a 16) 1 h112) (And.intro (forced (a 17) 1 h116) (And.intro (forced (a 18) 0 h18) (And.intro (forced (a 19) 1 h121) (And.intro (forced (a 20) 1 h105) (And.intro (forced (a 21) 0 h25) (And.intro (forced (a 22) 2 h118) (And.intro (forced (a 23) 1 h120) (And.intro (forced (a 24) 4 h107) (And.intro (forced (a 25) 1 h117) (And.intro (forced (a 26) 1 h119) (And.intro (forced (a 27) 1 h122) (And.intro (forced (a 28) 1 h109) (And.intro (forced (a 29) 6 h111) (And.intro (forced (a 30) 2 h113) (forced (a 31) 0 h67))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_182
