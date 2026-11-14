import PartitionData205_161
import PartitionPiece205_161_0
import PartitionPiece205_161_1
import PartitionPiece205_161_2
import PartitionPiece205_161_3
import PartitionPiece205_161_4
import PartitionPiece205_161_5
namespace PartitionCover205_161
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2,3,4,5,6])
    (start2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53])
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
  have group1 := chunk0 a start2 start0 c1
  have h2 := group1
  have group3 := chunk1 a h2 start0 start4 start8 c1 c2 c3
  rcases group3 with ⟨h4,h5,h6⟩
  have group7 := chunk2 a h6 start0 start3 h4 c3 c7
  rcases group7 with ⟨h8,h9⟩
  have group10 := chunk3 a h9 h4 start6 c7 c8
  rcases group10 with ⟨h11,h12⟩
  have group13 := chunk4 a h12 h4 start10 c8 c9
  rcases group13 with ⟨h14,h15⟩
  have group16 := chunk5 a h15 h4 c9
  have h17 := group16
  have group18 := chunk6 a h17 h4 start7 h11 c9 c10
  rcases group18 with ⟨h19,h20⟩
  have group21 := chunk7 a h20 h11 start11 c10 c11
  rcases group21 with ⟨h22,h23⟩
  have group24 := chunk8 a h23 h11 start5 h5 start12 c11 c12 c14
  rcases group24 with ⟨h25,h26,h27⟩
  have group28 := chunk9 a h27 h5 c14
  have h29 := group28
  have group30 := chunk10 a h29 h5 start13 h26 c14 c16
  rcases group30 with ⟨h31,h32⟩
  have group33 := chunk11 a h32 h26 c16
  have h34 := group33
  have group35 := chunk12 a h34 h26 start14 h14 c16 c18
  rcases group35 with ⟨h36,h37⟩
  have group38 := chunk13 a h37 h14 c18
  have h39 := group38
  have group40 := chunk14 a h39 h14 c18
  have h41 := group40
  have group42 := chunk15 a h41 h14 start15 h22 c18 c19
  rcases group42 with ⟨h43,h44⟩
  have group45 := chunk16 a h44 h22 c19
  have h46 := group45
  have group47 := chunk17 a h46 h22 c19
  have h48 := group47
  have group49 := chunk18 a h48 h22 start9 h8 c19 c20
  rcases group49 with ⟨h50,h51⟩
  have group52 := chunk19 a h51 h8 h31 h25 h36 h50 c20 c22 c23 c24 c27
  rcases group52 with ⟨h53,h54,h55,h56⟩
  have group57 := chunk20 a start1 h11 h26 c4 c5
  have h58 := group57
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h58) (And.intro (forced (a 2) 0 h4) (And.intro (forced (a 3) 0 h11) (And.intro (forced (a 4) 0 h5) (And.intro (forced (a 5) 0 h26) (And.intro (forced (a 6) 0 h14) (And.intro (forced (a 7) 0 h22) (And.intro (forced (a 8) 0 h54) (And.intro (forced (a 9) 0 h53) (And.intro (forced (a 10) 0 h19) (And.intro (forced (a 11) 0 h25) (And.intro (forced (a 12) 0 h31) (And.intro (forced (a 13) 0 h55) (And.intro (forced (a 14) 0 h43) (forced (a 15) 0 h56)))))))))))))))
#print axioms cover
end PartitionCover205_161
