import PartitionData205_177
import PartitionPiece205_177_0
import PartitionPiece205_177_1
import PartitionPiece205_177_2
namespace PartitionCover205_177
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0,1,2])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0,1,2,3,4,5])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1])
    (start14 : a 14 ∈ [0,1])
    (start15 : a 15 ∈ [0,1,2,3])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0,1])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0,1,2])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1])
    (start23 : a 23 ∈ [0,1,2,3,4,5,6,7,8])
    (start24 : a 24 ∈ [0,1,2,3])
    (start25 : a 25 ∈ [0,1])
    (start26 : a 26 ∈ [0,1,2,3])
    (start27 : a 27 ∈ [0,1,2,3])
    (start28 : a 28 ∈ [0,1,2,3,4,5])
    (start29 : a 29 ∈ [0,1,2,3])
    (start30 : a 30 ∈ [0,1,2,3])
    (start31 : a 31 ∈ [0,1])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=1 ∧ a 3=2 ∧ a 4=4 ∧ a 5=4 ∧ a 6=4 ∧ a 7=5 ∧ a 8=2 ∧ a 9=1 ∧ a 10=2 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=1 ∧ a 15=1 ∧ a 16=1 ∧ a 17=1 ∧ a 18=1 ∧ a 19=0 ∧ a 20=8 ∧ a 21=0 ∧ a 22=0 ∧ a 23=2 ∧ a 24=2 ∧ a 25=0 ∧ a 26=2 ∧ a 27=1 ∧ a 28=3 ∧ a 29=1 ∧ a 30=2 ∧ a 31=1) := by
  have group1 := chunk0 a start4 start0 start8 start3 start2 start10 start7 start5 start6 c2 c3 c9 c11 c13 c16 c17
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8⟩
  have group9 := chunk1 a h8 h2 start20 h6 h7 start21 start22 c17 c19 c20 c22 c25
  rcases group9 with ⟨h10,h11,h12,h13,h14⟩
  have group15 := chunk2 a start23 h12 start12 h3 start11 start9 start15 start27 start13 start28 c27 c30 c32 c38 c39 c40 c42
  rcases group15 with ⟨h16,h17,h18,h19,h20,h21,h22⟩
  have group23 := chunk3 a h22 h17 start19 start17 h13 h11 h14 h16 start29 start30 start25 h20 start26 c42 c52 c53 c61 c63 c64 c66 c71 c74
  rcases group23 with ⟨h24,h25,h26,h27,h28,h29,h30,h31⟩
  have group32 := chunk4 a h31 h29 start24 h30 c68 c74
  rcases group32 with ⟨h33,h34⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q35 | q36
  · have h37 : a 1 ∈ [0] := List.mem_singleton.mpr q35
    have group38 := chunk5 a start9 h37 start17 h3 h5 start14 h19 h29 start31 start16 start18 h33 h16 h34 h24 h20 h28 c7 c8 c28 c29 c36 c45 c46 c47 c48 c49 c57 c67 c69 c70 c73 c76
    rcases group38 with ⟨h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53,h54⟩
    have group55 := chunk6 a start2 h48 h10 h43 h12 h44 h27 h52 h4 h2 h7 c12 c13 c17 c20 c24 c26 c62
    rcases group55 with ⟨h56,h57,h58,h59,h60,h61,h62⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h37) (And.intro (forced (a 2) 0 h56) (And.intro (forced (a 3) 0 h60) (And.intro (forced (a 4) 0 h61) (And.intro (forced (a 5) 0 h62) (And.intro (forced (a 6) 0 h57) (And.intro (forced (a 7) 0 h58) (And.intro (forced (a 8) 0 h41) (And.intro (forced (a 9) 0 h39) (And.intro (forced (a 10) 0 h42) (And.intro (forced (a 11) 0 h18) (And.intro (forced (a 12) 0 h17) (And.intro (forced (a 13) 0 h21) (And.intro (forced (a 14) 0 h43) (And.intro (forced (a 15) 0 h44) (And.intro (forced (a 16) 0 h47) (And.intro (forced (a 17) 0 h40) (And.intro (forced (a 18) 0 h48) (And.intro (forced (a 19) 0 h25) (And.intro (forced (a 20) 0 h59) (And.intro (forced (a 21) 0 h26) (And.intro (forced (a 22) 0 h14) (And.intro (forced (a 23) 0 h50) (And.intro (forced (a 24) 0 h51) (And.intro (forced (a 25) 0 h30) (And.intro (forced (a 26) 0 h49) (And.intro (forced (a 27) 0 h53) (And.intro (forced (a 28) 0 h52) (And.intro (forced (a 29) 0 h54) (And.intro (forced (a 30) 0 h45) (forced (a 31) 0 h46))))))))))))))))))))))))))))))))
  · have h63 : a 1 ∈ [1] := List.mem_singleton.mpr q36
    have group64 := chunk7 a start9 h63 start17 h3 h5 start14 h19 h29 start31 start16 start18 h33 h16 h34 h24 h20 h28 c7 c8 c28 c29 c36 c45 c46 c47 c48 c49 c57 c67 c69 c70 c73 c76
    rcases group64 with ⟨h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78,h79,h80⟩
    have group81 := chunk8 a start2 h74 h10 h69 h12 h70 h27 h78 h4 h2 h7 c12 c13 c17 c20 c24 c26 c62
    rcases group81 with ⟨h82,h83,h84,h85,h86,h87,h88⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h63) (And.intro (forced (a 2) 1 h82) (And.intro (forced (a 3) 2 h86) (And.intro (forced (a 4) 4 h87) (And.intro (forced (a 5) 4 h88) (And.intro (forced (a 6) 4 h83) (And.intro (forced (a 7) 5 h84) (And.intro (forced (a 8) 2 h67) (And.intro (forced (a 9) 1 h65) (And.intro (forced (a 10) 2 h68) (And.intro (forced (a 11) 0 h18) (And.intro (forced (a 12) 0 h17) (And.intro (forced (a 13) 0 h21) (And.intro (forced (a 14) 1 h69) (And.intro (forced (a 15) 1 h70) (And.intro (forced (a 16) 1 h73) (And.intro (forced (a 17) 1 h66) (And.intro (forced (a 18) 1 h74) (And.intro (forced (a 19) 0 h25) (And.intro (forced (a 20) 8 h85) (And.intro (forced (a 21) 0 h26) (And.intro (forced (a 22) 0 h14) (And.intro (forced (a 23) 2 h76) (And.intro (forced (a 24) 2 h77) (And.intro (forced (a 25) 0 h30) (And.intro (forced (a 26) 2 h75) (And.intro (forced (a 27) 1 h79) (And.intro (forced (a 28) 3 h78) (And.intro (forced (a 29) 1 h80) (And.intro (forced (a 30) 2 h71) (forced (a 31) 1 h72))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_177
