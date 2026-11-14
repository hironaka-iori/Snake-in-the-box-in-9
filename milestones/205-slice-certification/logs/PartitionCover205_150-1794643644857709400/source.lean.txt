import PartitionData205_150
import PartitionPiece205_150_0
import PartitionPiece205_150_1
import PartitionPiece205_150_2
import PartitionPiece205_150_3
namespace PartitionCover205_150
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2,3])
    (start2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start3 : a 3 ∈ [0,1,2,3,4,5])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35])
    (start8 : a 8 ∈ [0,1,2,3,4,5])
    (start9 : a 9 ∈ [0,1,2,3])
    (start10 : a 10 ∈ [0,1,2,3,4,5])
    (start11 : a 11 ∈ [0,1,2,3])
    (start12 : a 12 ∈ [0,1,2,3,4,5])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
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
  have group1 := chunk0 a start1 start5 c5
  rcases group1 with ⟨h2,h3⟩
  have group4 := chunk1 a h3 h2 c5
  have h5 := group4
  have group6 := chunk2 a h5 h2 start9 start3 start2 start7 c5 c6 c7 c10
  rcases group6 with ⟨h7,h8,h9,h10⟩
  have group11 := chunk3 a h10 h9 start11 start4 h7 start6 c10 c11 c12 c13
  rcases group11 with ⟨h12,h13,h14,h15,h16⟩
  have group17 := chunk4 a h16 h15 c13
  have h18 := group17
  have group19 := chunk5 a h18 h15 start12 c13 c14
  rcases group19 with ⟨h20,h21,h22⟩
  have group23 := chunk6 a h22 h21 h7 h12 c14 c15
  rcases group23 with ⟨h24,h25,h26⟩
  have group27 := chunk7 a h26 h25 start13 c15 c16
  rcases group27 with ⟨h28,h29⟩
  have group30 := chunk8 a h29 h25 h20 h28 c16 c17
  rcases group30 with ⟨h31,h32⟩
  have group33 := chunk9 a h32 h28 start14 start15 c17 c18 c19
  rcases group33 with ⟨h34,h35,h36⟩
  have group37 := chunk10 a h36 h28 start8 h8 c19 c20
  rcases group37 with ⟨h38,h39⟩
  have group40 := chunk11 a h8 h39 start10 h24 h14 h38 h35 h2 h13 start2 h34 c4 c8 c20 c21 c22 c23 c25 c27 c29
  rcases group40 with ⟨h41,h42,h43,h44,h45,h46,h47,h48⟩
  have group49 := chunk12 a h48 h34 h13 h28 c8 c10
  rcases group49 with ⟨h50,h51⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h47) (And.intro (forced (a 2) 0 h50) (And.intro (forced (a 3) 0 h51) (And.intro (forced (a 4) 0 h21) (And.intro (forced (a 5) 0 h25) (And.intro (forced (a 6) 0 h34) (And.intro (forced (a 7) 0 h28) (And.intro (forced (a 8) 0 h43) (And.intro (forced (a 9) 0 h41) (And.intro (forced (a 10) 0 h42) (And.intro (forced (a 11) 0 h44) (And.intro (forced (a 12) 0 h24) (And.intro (forced (a 13) 0 h31) (And.intro (forced (a 14) 0 h46) (forced (a 15) 0 h45)))))))))))))))
#print axioms cover
end PartitionCover205_150
