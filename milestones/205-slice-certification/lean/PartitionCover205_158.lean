import PartitionData205_158
import PartitionPiece205_158_0
import PartitionPiece205_158_1
import PartitionPiece205_158_2
namespace PartitionCover205_158
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1,2])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
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
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0) := by
  have group1 := chunk0 a start4 start0 start8 c2 c3
  rcases group1 with ⟨h2,h3⟩
  have group4 := chunk1 a h3 start0 start5 start1 c3 c5
  rcases group4 with ⟨h5,h6⟩
  have group7 := chunk2 a h6 start1 start9 c5 c6
  rcases group7 with ⟨h8,h9⟩
  have group10 := chunk3 a start2 start3 start6 start10 c7 c8 c9
  rcases group10 with ⟨h11,h12,h13⟩
  have group14 := chunk4 a h13 h11 h8 h2 start12 c9 c12 c14
  rcases group14 with ⟨h15,h16,h17⟩
  have group18 := chunk5 a h17 h2 start7 h16 c14 c15
  rcases group18 with ⟨h19,h20⟩
  have group21 := chunk6 a h20 h16 start13 start14 h12 c15 c16 c18
  rcases group21 with ⟨h22,h23,h24⟩
  have group25 := chunk7 a h24 h12 start15 h22 c18 c19
  rcases group25 with ⟨h26,h27⟩
  have group28 := chunk8 a h27 h22 h5 h15 start11 h9 c19 c21 c23
  rcases group28 with ⟨h29,h30,h31,h32⟩
  have group33 := chunk9 a h32 h9 h23 h19 start3 h22 h30 c10 c20 c23 c24 c28
  rcases group33 with ⟨h34,h35,h36,h37,h38⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h11) (And.intro (forced (a 3) 0 h37) (And.intro (forced (a 4) 0 h2) (And.intro (forced (a 5) 0 h16) (And.intro (forced (a 6) 0 h12) (And.intro (forced (a 7) 0 h22) (And.intro (forced (a 8) 0 h30) (And.intro (forced (a 9) 0 h38) (And.intro (forced (a 10) 0 h31) (And.intro (forced (a 11) 0 h34) (And.intro (forced (a 12) 0 h36) (And.intro (forced (a 13) 0 h35) (And.intro (forced (a 14) 0 h26) (forced (a 15) 0 h29)))))))))))))))
#print axioms cover
end PartitionCover205_158
