import PartitionData205_154
import PartitionPiece205_154_0
import PartitionPiece205_154_1
import PartitionPiece205_154_2
namespace PartitionCover205_154
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31])
    (start9 : a 9 ∈ [0])
    (start10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (start11 : a 11 ∈ [0,1])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=1 ∧ a 3=1 ∧ a 4=4 ∧ a 5=6 ∧ a 6=4 ∧ a 7=6 ∧ a 8=16 ∧ a 9=0 ∧ a 10=8 ∧ a 11=1 ∧ a 12=4 ∧ a 13=4 ∧ a 14=4 ∧ a 15=4) := by
  have group1 := chunk0 a start4 start0 start8 c2 c3
  rcases group1 with ⟨h2,h3⟩
  have group4 := chunk1 a h3 start0 start5 start1 c3 c5
  rcases group4 with ⟨h5,h6⟩
  have group7 := chunk2 a h6 start1 start10 start2 c5 c9
  rcases group7 with ⟨h8,h9⟩
  have group10 := chunk3 a h9 start2 h2 h8 start6 start12 c9 c12 c13 c14
  rcases group10 with ⟨h11,h12,h13,h14⟩
  have group15 := chunk4 a start7 h8 start13 c15 c16
  rcases group15 with ⟨h16,h17⟩
  have group18 := chunk5 a start14 h13 start15 h16 h5 start9 h11 c18 c19 c20 c21
  rcases group18 with ⟨h19,h20,h21⟩
  have group22 := chunk6 a h11 h21 h20 h17 c21 c30
  rcases group22 with ⟨h23,h24⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q25 | q26
  · have h27 : a 1 ∈ [0] := List.mem_singleton.mpr q25
    have group28 := chunk7 a start3 h27 h8 start2 h13 h16 start11 h12 h14 h17 h19 h24 h23 h21 c4 c5 c7 c8 c10 c11 c12 c14 c16 c18 c19 c21 c26
    rcases group28 with ⟨h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h27) (And.intro (forced (a 2) 0 h31) (And.intro (forced (a 3) 0 h29) (And.intro (forced (a 4) 0 h35) (And.intro (forced (a 5) 0 h30) (And.intro (forced (a 6) 0 h32) (And.intro (forced (a 7) 0 h33) (And.intro (forced (a 8) 0 h41) (And.intro (forced (a 9) 0 start9) (And.intro (forced (a 10) 0 h40) (And.intro (forced (a 11) 0 h34) (And.intro (forced (a 12) 0 h36) (And.intro (forced (a 13) 0 h37) (And.intro (forced (a 14) 0 h38) (forced (a 15) 0 h39))))))))))))))))
  · have h42 : a 1 ∈ [1] := List.mem_singleton.mpr q26
    have group43 := chunk8 a start3 h42 h8 start2 h13 h16 start11 h12 h14 h17 h19 h24 h23 h21 c4 c5 c7 c8 c10 c11 c12 c14 c16 c18 c19 c21 c26
    rcases group43 with ⟨h44,h45,h46,h47,h48,h49,h50,h51,h52,h53,h54,h55,h56⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h42) (And.intro (forced (a 2) 1 h46) (And.intro (forced (a 3) 1 h44) (And.intro (forced (a 4) 4 h50) (And.intro (forced (a 5) 6 h45) (And.intro (forced (a 6) 4 h47) (And.intro (forced (a 7) 6 h48) (And.intro (forced (a 8) 16 h56) (And.intro (forced (a 9) 0 start9) (And.intro (forced (a 10) 8 h55) (And.intro (forced (a 11) 1 h49) (And.intro (forced (a 12) 4 h51) (And.intro (forced (a 13) 4 h52) (And.intro (forced (a 14) 4 h53) (forced (a 15) 4 h54))))))))))))))))
#print axioms cover
end PartitionCover205_154
