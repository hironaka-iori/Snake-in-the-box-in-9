import PartitionData205_114
import PartitionPiece205_114_0
import PartitionPiece205_114_1
import PartitionPiece205_114_2
namespace PartitionCover205_114
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1,2,3,4,5,6,7])
    (start3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1,2,3])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7])
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
      (a 0=0 ∧ a 1=0 ∧ a 2=6 ∧ a 3=3 ∧ a 4=3 ∧ a 5=3 ∧ a 6=6 ∧ a 7=18 ∧ a 8=3 ∧ a 9=3 ∧ a 10=18 ∧ a 11=18 ∧ a 12=18 ∧ a 13=6 ∧ a 14=6 ∧ a 15=6) := by
  have group1 := chunk0 a start2 start0 start9 start1 start3 c1 c6 c7
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 h2 start6 start10 c7 c8 c9
  rcases group5 with ⟨h6,h7,h8⟩
  have group9 := chunk2 a h8 h2 start11 h6 c9 c11
  rcases group9 with ⟨h10,h11⟩
  have group12 := chunk3 a h11 h6 start4 start5 start12 c11 c12 c14
  rcases group12 with ⟨h13,h14,h15,h16⟩
  have group17 := chunk4 a h16 h14 c14
  have h18 := group17
  have group19 := chunk5 a start7 h15 c15
  have h20 := group19
  have group21 := chunk6 a h20 h15 start13 h7 start14 start15 c15 c16 c17 c18 c19
  rcases group21 with ⟨h22,h23,h24,h25⟩
  have group26 := chunk7 a h25 h22 start8 h3 h10 h18 h13 c19 c20 c21 c22 c23
  rcases group26 with ⟨h27,h28,h29,h30,h31⟩
  have group32 := chunk8 a h23 h3 h29 h31 c24 c25
  rcases group32 with ⟨h33,h34⟩
  rcases (show a 2=0 ∨ a 2=6 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h2) with q35 | q36
  · have h37 : a 2 ∈ [0] := List.mem_singleton.mpr q35
    have group38 := chunk9 a h6 h37 h7 h34 h22 h14 h30 h15 h33 h24 h27 h28 h3 h31 c7 c8 c9 c10 c13 c14 c15 c16 c18 c19 c21 c24 c25
    rcases group38 with ⟨h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h37) (And.intro (forced (a 3) 0 h39) (And.intro (forced (a 4) 0 h43) (And.intro (forced (a 5) 0 h45) (And.intro (forced (a 6) 0 h40) (And.intro (forced (a 7) 0 h42) (And.intro (forced (a 8) 0 h49) (And.intro (forced (a 9) 0 h50) (And.intro (forced (a 10) 0 h41) (And.intro (forced (a 11) 0 h51) (And.intro (forced (a 12) 0 h44) (And.intro (forced (a 13) 0 h46) (And.intro (forced (a 14) 0 h47) (forced (a 15) 0 h48))))))))))))))))
  · have h52 : a 2 ∈ [6] := List.mem_singleton.mpr q36
    have group53 := chunk10 a h6 h52 h7 h34 h22 h14 h30 h15 h33 h24 h27 h28 h3 h31 c7 c8 c9 c10 c13 c14 c15 c16 c18 c19 c21 c24 c25
    rcases group53 with ⟨h54,h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65,h66⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 6 h52) (And.intro (forced (a 3) 3 h54) (And.intro (forced (a 4) 3 h58) (And.intro (forced (a 5) 3 h60) (And.intro (forced (a 6) 6 h55) (And.intro (forced (a 7) 18 h57) (And.intro (forced (a 8) 3 h64) (And.intro (forced (a 9) 3 h65) (And.intro (forced (a 10) 18 h56) (And.intro (forced (a 11) 18 h66) (And.intro (forced (a 12) 18 h59) (And.intro (forced (a 13) 6 h61) (And.intro (forced (a 14) 6 h62) (forced (a 15) 6 h63))))))))))))))))
#print axioms cover
end PartitionCover205_114
