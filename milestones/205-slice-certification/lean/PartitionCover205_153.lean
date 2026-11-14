import PartitionData205_153
import PartitionPiece205_153_0
import PartitionPiece205_153_1
import PartitionPiece205_153_2
import PartitionPiece205_153_3
namespace PartitionCover205_153
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2,3])
    (start2 : a 2 ∈ [0,1,2])
    (start3 : a 3 ∈ [0,1,2,3,4,5,6,7])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    (c26 : edge r26 (a 10) (a 14)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    (c28 : edge r28 (a 12) (a 13)=true)
    (c29 : edge r29 (a 12) (a 14)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    (c31 : edge r31 (a 14) (a 15)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0) ∨
      (a 0=0 ∧ a 1=1 ∧ a 2=0 ∧ a 3=2 ∧ a 4=1 ∧ a 5=12 ∧ a 6=1 ∧ a 7=12 ∧ a 8=1 ∧ a 9=2 ∧ a 10=1 ∧ a 11=2 ∧ a 12=3 ∧ a 13=1 ∧ a 14=3 ∧ a 15=1) := by
  have group1 := chunk0 a start4 start0 c2
  have h2 := group1
  have group3 := chunk1 a start5 start1 c5
  have h4 := group3
  have group5 := chunk2 a h4 start1 c5
  have h6 := group5
  have group7 := chunk3 a h6 start1 start9 c5 c6
  rcases group7 with ⟨h8,h9⟩
  have group10 := chunk4 a start3 start2 start7 start11 c7 c10 c11
  rcases group10 with ⟨h11,h12,h13⟩
  have group14 := chunk5 a h8 h2 start6 c12 c13
  rcases group14 with ⟨h15,h16⟩
  have group17 := chunk6 a h16 h2 start12 h12 h15 c13 c14 c15
  rcases group17 with ⟨h18,h19,h20⟩
  have group21 := chunk7 a h20 h15 c15
  have h22 := group21
  have group23 := chunk8 a h22 h15 c15
  have h24 := group23
  have group25 := chunk9 a h24 h15 start13 c15 c16
  rcases group25 with ⟨h26,h27⟩
  have group28 := chunk10 a h27 h15 start14 h18 c16 c18
  rcases group28 with ⟨h29,h30⟩
  have group31 := chunk11 a start15 h26 c19
  have h32 := group31
  have group33 := chunk12 a h32 h26 h9 start8 h19 h13 c19 c20 c22 c23
  rcases group33 with ⟨h34,h35,h36,h37⟩
  have group38 := chunk13 a start10 h37 h30 h19 start1 h15 start2 h18 h11 h26 c5 c8 c10 c25 c26 c29
  rcases group38 with ⟨h39,h40,h41,h42,h43⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h41) with q44 | q45
  · have h46 : a 1 ∈ [0] := List.mem_singleton.mpr q44
    have group47 := chunk14 a h43 h46 h15 h35 h26 h37 h2 h18 h19 h29 h40 h36 h39 h34 c4 c5 c6 c10 c11 c12 c13 c14 c16 c18 c20 c21 c27
    rcases group47 with ⟨h48,h49,h50,h51,h52,h53,h54,h55,h56,h57,h58,h59,h60⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h46) (And.intro (forced (a 2) 0 h42) (And.intro (forced (a 3) 0 h48) (And.intro (forced (a 4) 0 h53) (And.intro (forced (a 5) 0 h49) (And.intro (forced (a 6) 0 h54) (And.intro (forced (a 7) 0 h51) (And.intro (forced (a 8) 0 h58) (And.intro (forced (a 9) 0 h50) (And.intro (forced (a 10) 0 h59) (And.intro (forced (a 11) 0 h52) (And.intro (forced (a 12) 0 h55) (And.intro (forced (a 13) 0 h56) (And.intro (forced (a 14) 0 h57) (forced (a 15) 0 h60))))))))))))))))
  · have h61 : a 1 ∈ [1] := List.mem_singleton.mpr q45
    have group62 := chunk15 a h43 h61 h15 h35 h26 h37 h2 h18 h19 h29 h40 h36 h39 h34 c4 c5 c6 c10 c11 c12 c13 c14 c16 c18 c20 c21 c27
    rcases group62 with ⟨h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h61) (And.intro (forced (a 2) 0 h42) (And.intro (forced (a 3) 2 h63) (And.intro (forced (a 4) 1 h68) (And.intro (forced (a 5) 12 h64) (And.intro (forced (a 6) 1 h69) (And.intro (forced (a 7) 12 h66) (And.intro (forced (a 8) 1 h73) (And.intro (forced (a 9) 2 h65) (And.intro (forced (a 10) 1 h74) (And.intro (forced (a 11) 2 h67) (And.intro (forced (a 12) 3 h70) (And.intro (forced (a 13) 1 h71) (And.intro (forced (a 14) 3 h72) (forced (a 15) 1 h75))))))))))))))))
#print axioms cover
end PartitionCover205_153
