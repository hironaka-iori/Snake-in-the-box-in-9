import PartitionData205_199
import PartitionPiece205_199_0
import PartitionPiece205_199_1
import PartitionPiece205_199_2
namespace PartitionCover205_199
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1,2,3,4,5])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0,1,2])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7])
    (start10 : a 10 ∈ [0,1,2])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (start12 : a 12 ∈ [0,1,2,3])
    (start13 : a 13 ∈ [0,1,2,3,4,5])
    (start14 : a 14 ∈ [0,1,2])
    (start15 : a 15 ∈ [0,1,2,3,4,5])
    (start16 : a 16 ∈ [0,1,2,3,4,5])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start18 : a 18 ∈ [0,1,2])
    (start19 : a 19 ∈ [0,1,2,3,4,5])
    (start20 : a 20 ∈ [0,1,2,3,4,5])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5])
    (start23 : a 23 ∈ [0,1,2,3,4,5])
    (start24 : a 24 ∈ [0,1,2,3,4,5])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start26 : a 26 ∈ [0,1,2,3,4,5,6,7])
    (start27 : a 27 ∈ [0,1,2,3,4,5])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7])
    (start29 : a 29 ∈ [0,1,2])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7])
    (start31 : a 31 ∈ [0,1,2])
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
      (a 0=0 ∧ a 1=0 ∧ a 2=1 ∧ a 3=1 ∧ a 4=2 ∧ a 5=1 ∧ a 6=0 ∧ a 7=1 ∧ a 8=1 ∧ a 9=4 ∧ a 10=1 ∧ a 11=1 ∧ a 12=2 ∧ a 13=1 ∧ a 14=0 ∧ a 15=1 ∧ a 16=3 ∧ a 17=6 ∧ a 18=0 ∧ a 19=4 ∧ a 20=0 ∧ a 21=3 ∧ a 22=4 ∧ a 23=4 ∧ a 24=3 ∧ a 25=6 ∧ a 26=4 ∧ a 27=4 ∧ a 28=4 ∧ a 29=1 ∧ a 30=4 ∧ a 31=2) := by
  have group1 := chunk0 a start2 start0 start4 start16 start9 start1 c1 c2 c4 c7
  rcases group1 with ⟨h2,h3,h4,h5⟩
  have group6 := chunk1 a start17 start1 start3 h2 start6 start10 start18 c8 c9 c10 c11 c12
  rcases group6 with ⟨h7,h8,h9,h10,h11⟩
  have group12 := chunk2 a h11 h2 start7 h8 start11 start5 h3 start12 c12 c13 c14 c16 c18
  rcases group12 with ⟨h13,h14,h15,h16,h17⟩
  have group18 := chunk3 a h17 h3 start20 start13 h16 start21 start14 h9 start22 c18 c19 c21 c22 c24 c25
  rcases group18 with ⟨h19,h20,h21,h22,h23,h24⟩
  have group25 := chunk4 a h24 h9 start15 h14 start25 h5 h15 h10 start26 c25 c26 c34 c35 c37
  rcases group25 with ⟨h26,h27,h28,h29,h30⟩
  have group31 := chunk5 a h30 h10 h27 h29 start27 start28 h19 start29 h21 start31 h7 h4 start24 c37 c38 c39 c42 c44 c47 c48 c51
  rcases group31 with ⟨h32,h33,h34,h35,h36,h37,h38,h39⟩
  have group40 := chunk6 a h39 h4 h28 h38 start19 h13 start23 h34 h20 h22 h35 c51 c54 c55 c58 c59 c60 c62
  rcases group40 with ⟨h41,h42,h43,h44,h45,h46,h47⟩
  have group48 := chunk7 a h47 h46 start30 h26 h32 c62 c66 c74
  rcases group48 with ⟨h49,h50⟩
  rcases (show a 2=0 ∨ a 2=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h2) with q51 | q52
  · have h53 : a 2 ∈ [0] := List.mem_singleton.mpr q51
    have group54 := chunk8 a h8 h53 h10 h14 h33 start8 h19 h41 h29 h32 h45 h49 h21 h36 h37 h4 h43 c9 c11 c13 c26 c29 c30 c31 c35 c37 c39 c42 c43 c44 c47 c51 c59
    rcases group54 with ⟨h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65,h66,h67,h68,h69,h70⟩
    have group71 := chunk9 a h44 h68 h42 h61 h50 h63 h3 h60 h16 h66 h5 h59 h38 h69 h22 h26 c18 c21 c28 c48 c53 c65 c67 c68 c74
    rcases group71 with ⟨h72,h73,h74,h75,h76,h77,h78,h79,h80⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h53) (And.intro (forced (a 3) 0 h55) (And.intro (forced (a 4) 0 h75) (And.intro (forced (a 5) 0 h76) (And.intro (forced (a 6) 0 h9) (And.intro (forced (a 7) 0 h57) (And.intro (forced (a 8) 0 h59) (And.intro (forced (a 9) 0 h77) (And.intro (forced (a 10) 0 h56) (And.intro (forced (a 11) 0 h62) (And.intro (forced (a 12) 0 h60) (And.intro (forced (a 13) 0 h66) (And.intro (forced (a 14) 0 h23) (And.intro (forced (a 15) 0 h58) (And.intro (forced (a 16) 0 h69) (And.intro (forced (a 17) 0 h78) (And.intro (forced (a 18) 0 h13) (And.intro (forced (a 19) 0 h70) (And.intro (forced (a 20) 0 h46) (And.intro (forced (a 21) 0 h79) (And.intro (forced (a 22) 0 h80) (And.intro (forced (a 23) 0 h72) (And.intro (forced (a 24) 0 h61) (And.intro (forced (a 25) 0 h73) (And.intro (forced (a 26) 0 h63) (And.intro (forced (a 27) 0 h64) (And.intro (forced (a 28) 0 h65) (And.intro (forced (a 29) 0 h67) (And.intro (forced (a 30) 0 h74) (forced (a 31) 0 h68))))))))))))))))))))))))))))))))
  · have h81 : a 2 ∈ [1] := List.mem_singleton.mpr q52
    have group82 := chunk10 a h8 h81 h10 h14 h33 start8 h19 h41 h29 h32 h45 h49 h21 h36 h37 h4 h43 c9 c11 c13 c26 c29 c30 c31 c35 c37 c39 c42 c43 c44 c47 c51 c59
    rcases group82 with ⟨h83,h84,h85,h86,h87,h88,h89,h90,h91,h92,h93,h94,h95,h96,h97,h98⟩
    have group99 := chunk11 a h44 h96 h42 h89 h50 h91 h3 h88 h16 h94 h5 h87 h38 h97 h22 h26 c18 c21 c28 c48 c53 c65 c67 c68 c74
    rcases group99 with ⟨h100,h101,h102,h103,h104,h105,h106,h107,h108⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 1 h81) (And.intro (forced (a 3) 1 h83) (And.intro (forced (a 4) 2 h103) (And.intro (forced (a 5) 1 h104) (And.intro (forced (a 6) 0 h9) (And.intro (forced (a 7) 1 h85) (And.intro (forced (a 8) 1 h87) (And.intro (forced (a 9) 4 h105) (And.intro (forced (a 10) 1 h84) (And.intro (forced (a 11) 1 h90) (And.intro (forced (a 12) 2 h88) (And.intro (forced (a 13) 1 h94) (And.intro (forced (a 14) 0 h23) (And.intro (forced (a 15) 1 h86) (And.intro (forced (a 16) 3 h97) (And.intro (forced (a 17) 6 h106) (And.intro (forced (a 18) 0 h13) (And.intro (forced (a 19) 4 h98) (And.intro (forced (a 20) 0 h46) (And.intro (forced (a 21) 3 h107) (And.intro (forced (a 22) 4 h108) (And.intro (forced (a 23) 4 h100) (And.intro (forced (a 24) 3 h89) (And.intro (forced (a 25) 6 h101) (And.intro (forced (a 26) 4 h91) (And.intro (forced (a 27) 4 h92) (And.intro (forced (a 28) 4 h93) (And.intro (forced (a 29) 1 h95) (And.intro (forced (a 30) 4 h102) (forced (a 31) 2 h96))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_199
