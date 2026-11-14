import PartitionData205_171
import PartitionPiece205_171_0
import PartitionPiece205_171_1
import PartitionPiece205_171_2
namespace PartitionCover205_171
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7])
    (start9 : a 9 ∈ [0,1,2,3,4,5])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (start12 : a 12 ∈ [0,1,2,3,4,5])
    (start13 : a 13 ∈ [0,1,2])
    (start14 : a 14 ∈ [0,1,2])
    (start15 : a 15 ∈ [0,1,2,3])
    (start16 : a 16 ∈ [0,1,2,3])
    (start17 : a 17 ∈ [0,1])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0,1])
    (start20 : a 20 ∈ [0,1,2,3,4,5])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7])
    (start24 : a 24 ∈ [0,1])
    (start25 : a 25 ∈ [0,1,2,3,4,5])
    (start26 : a 26 ∈ [0,1,2,3])
    (start27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7])
    (start29 : a 29 ∈ [0,1,2,3,4,5,6,7])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7])
    (start31 : a 31 ∈ [0,1,2,3,4,5,6,7,8])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=2 ∧ a 3=0 ∧ a 4=1 ∧ a 5=4 ∧ a 6=2 ∧ a 7=1 ∧ a 8=4 ∧ a 9=3 ∧ a 10=4 ∧ a 11=6 ∧ a 12=1 ∧ a 13=0 ∧ a 14=2 ∧ a 15=3 ∧ a 16=2 ∧ a 17=1 ∧ a 18=1 ∧ a 19=1 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=5 ∧ a 24=0 ∧ a 25=0 ∧ a 26=2 ∧ a 27=1 ∧ a 28=4 ∧ a 29=4 ∧ a 30=4 ∧ a 31=6) := by
  have group1 := chunk0 a start2 start0 start4 start8 start16 start6 c1 c2 c3 c4 c10
  rcases group1 with ⟨h2,h3,h4,h5,h6⟩
  have group7 := chunk1 a h6 h2 start10 start11 start3 c10 c11 c14
  rcases group7 with ⟨h8,h9,h10⟩
  have group11 := chunk2 a h10 start3 start5 h3 h8 start12 start20 start13 c14 c16 c17 c18 c19 c21
  rcases group11 with ⟨h12,h13,h14,h15,h16,h17⟩
  have group18 := chunk3 a h17 h13 start21 start22 h14 start9 h4 h12 start25 c21 c22 c25 c28 c32 c34
  rcases group18 with ⟨h19,h20,h21,h22,h23,h24⟩
  have group25 := chunk4 a h24 h22 start14 h9 start26 start15 h23 start27 c34 c36 c37 c38 c39
  rcases group25 with ⟨h26,h27,h28,h29,h30⟩
  have group31 := chunk5 a start28 h15 start29 h19 start30 h27 start31 h29 c42 c44 c46 c47
  rcases group31 with ⟨h32,h33,h34,h35⟩
  have group36 := chunk6 a h35 h29 h16 h5 h21 start18 start23 start19 h30 h34 c47 c50 c56 c58 c59 c66
  rcases group36 with ⟨h37,h38,h39,h40,h41,h42⟩
  have group43 := chunk7 a start24 h28 h26 h41 h37 h33 c69 c71 c75 c78
  rcases group43 with ⟨h44,h45,h46⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q47 | q48
  · have h49 : a 1 ∈ [0] := List.mem_singleton.mpr q47
    have group50 := chunk8 a h22 h49 start17 h4 h9 h15 h23 h27 h28 h29 h41 h32 h42 h46 h5 start18 start19 c7 c8 c28 c29 c30 c32 c36 c37 c38 c39 c42 c46 c47 c48 c49 c52
    rcases group50 with ⟨h51,h52,h53,h54,h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65,h66⟩
    have group67 := chunk9 a h40 h66 h33 h61 h2 h65 h3 h55 h14 h57 start7 h59 h13 c12 c16 c18 c24 c26 c58 c76
    rcases group67 with ⟨h68,h69,h70,h71,h72,h73,h74⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h49) (And.intro (forced (a 2) 0 h70) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h71) (And.intro (forced (a 5) 0 h74) (And.intro (forced (a 6) 0 h72) (And.intro (forced (a 7) 0 h73) (And.intro (forced (a 8) 0 h53) (And.intro (forced (a 9) 0 h51) (And.intro (forced (a 10) 0 h54) (And.intro (forced (a 11) 0 h56) (And.intro (forced (a 12) 0 h55) (And.intro (forced (a 13) 0 h19) (And.intro (forced (a 14) 0 h57) (And.intro (forced (a 15) 0 h59) (And.intro (forced (a 16) 0 h64) (And.intro (forced (a 17) 0 h52) (And.intro (forced (a 18) 0 h65) (And.intro (forced (a 19) 0 h66) (And.intro (forced (a 20) 0 h38) (And.intro (forced (a 21) 0 h20) (And.intro (forced (a 22) 0 h39) (And.intro (forced (a 23) 0 h68) (And.intro (forced (a 24) 0 h44) (And.intro (forced (a 25) 0 h45) (And.intro (forced (a 26) 0 h58) (And.intro (forced (a 27) 0 h60) (And.intro (forced (a 28) 0 h61) (And.intro (forced (a 29) 0 h69) (And.intro (forced (a 30) 0 h62) (forced (a 31) 0 h63))))))))))))))))))))))))))))))))
  · have h75 : a 1 ∈ [1] := List.mem_singleton.mpr q48
    have group76 := chunk10 a h22 h75 start17 h4 h9 h15 h23 h27 h28 h29 h41 h32 h42 h46 h5 start18 start19 c7 c8 c28 c29 c30 c32 c36 c37 c38 c39 c42 c46 c47 c48 c49 c52
    rcases group76 with ⟨h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90,h91,h92⟩
    have group93 := chunk11 a h40 h92 h33 h87 h2 h91 h3 h81 h14 h83 start7 h85 h13 c12 c16 c18 c24 c26 c58 c76
    rcases group93 with ⟨h94,h95,h96,h97,h98,h99,h100⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h75) (And.intro (forced (a 2) 2 h96) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 1 h97) (And.intro (forced (a 5) 4 h100) (And.intro (forced (a 6) 2 h98) (And.intro (forced (a 7) 1 h99) (And.intro (forced (a 8) 4 h79) (And.intro (forced (a 9) 3 h77) (And.intro (forced (a 10) 4 h80) (And.intro (forced (a 11) 6 h82) (And.intro (forced (a 12) 1 h81) (And.intro (forced (a 13) 0 h19) (And.intro (forced (a 14) 2 h83) (And.intro (forced (a 15) 3 h85) (And.intro (forced (a 16) 2 h90) (And.intro (forced (a 17) 1 h78) (And.intro (forced (a 18) 1 h91) (And.intro (forced (a 19) 1 h92) (And.intro (forced (a 20) 0 h38) (And.intro (forced (a 21) 0 h20) (And.intro (forced (a 22) 0 h39) (And.intro (forced (a 23) 5 h94) (And.intro (forced (a 24) 0 h44) (And.intro (forced (a 25) 0 h45) (And.intro (forced (a 26) 2 h84) (And.intro (forced (a 27) 1 h86) (And.intro (forced (a 28) 4 h87) (And.intro (forced (a 29) 4 h95) (And.intro (forced (a 30) 4 h88) (forced (a 31) 6 h89))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_171
