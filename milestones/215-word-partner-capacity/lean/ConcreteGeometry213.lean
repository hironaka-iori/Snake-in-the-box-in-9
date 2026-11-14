import ConcreteCoverage213
import ConcreteChunk213_00
import ConcreteChunk213_01
import ConcreteChunk213_02
import ConcreteChunk213_03
import ConcreteChunk213_04
import ConcreteChunk213_05
import ConcretePart213_chunk_30
import ConcretePart213_chunk_31
import ConcretePart213_chunk_32
import ConcretePart213_chunk_33
import ConcretePart213_chunk_34
import ConcretePart213_chunk_35
import ConcretePart213_chunk_36
import ConcretePart213_chunk_37
import ConcretePart213_chunk_38
import ConcretePart213_chunk_39
import ConcretePart213_chunk_40
import ConcretePart213_tail

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

private theorem all_from_take_drop {α : Type} (xs : List α) (p : α → Bool)
    (n : Nat) (hhead : (xs.take n).all p = true)
    (htail : (xs.drop n).all p = true) : xs.all p = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hmem : a ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using ha
  rcases List.mem_append.mp hmem with hh | ht
  · exact List.all_eq_true.mp hhead a hh
  · exact List.all_eq_true.mp htail a ht

section
attribute [local irreducible] requiredPairs makeCertificate validCertificate

private theorem valid_step (n : Nat)
    (hhead : ((requiredPairs.drop n).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true)
    (htail : (requiredPairs.drop (n + 32)).all
      (fun xy => validCertificate (makeCertificate xy)) = true) :
    (requiredPairs.drop n).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  apply all_from_take_drop (requiredPairs.drop n)
    (fun xy => validCertificate (makeCertificate xy)) 32 hhead
  simpa only [List.drop_drop, Nat.add_comm] using htail

private theorem required_pairs_valid :
    requiredPairs.all (fun xy => validCertificate (makeCertificate xy)) = true := by
  have h40 := valid_step 1280 valid_chunk_40 valid_tail
  have h39 := valid_step 1248 valid_chunk_39 h40
  have h38 := valid_step 1216 valid_chunk_38 h39
  have h37 := valid_step 1184 valid_chunk_37 h38
  have h36 := valid_step 1152 valid_chunk_36 h37
  have h35 := valid_step 1120 valid_chunk_35 h36
  have h34 := valid_step 1088 valid_chunk_34 h35
  have h33 := valid_step 1056 valid_chunk_33 h34
  have h32 := valid_step 1024 valid_chunk_32 h33
  have h31 := valid_step 992 valid_chunk_31 h32
  have h30 := valid_step 960 valid_chunk_30 h31
  have h29 := valid_step 928 valid_chunk_29 h30
  have h28 := valid_step 896 valid_chunk_28 h29
  have h27 := valid_step 864 valid_chunk_27 h28
  have h26 := valid_step 832 valid_chunk_26 h27
  have h25 := valid_step 800 valid_chunk_25 h26
  have h24 := valid_step 768 valid_chunk_24 h25
  have h23 := valid_step 736 valid_chunk_23 h24
  have h22 := valid_step 704 valid_chunk_22 h23
  have h21 := valid_step 672 valid_chunk_21 h22
  have h20 := valid_step 640 valid_chunk_20 h21
  have h19 := valid_step 608 valid_chunk_19 h20
  have h18 := valid_step 576 valid_chunk_18 h19
  have h17 := valid_step 544 valid_chunk_17 h18
  have h16 := valid_step 512 valid_chunk_16 h17
  have h15 := valid_step 480 valid_chunk_15 h16
  have h14 := valid_step 448 valid_chunk_14 h15
  have h13 := valid_step 416 valid_chunk_13 h14
  have h12 := valid_step 384 valid_chunk_12 h13
  have h11 := valid_step 352 valid_chunk_11 h12
  have h10 := valid_step 320 valid_chunk_10 h11
  have h9 := valid_step 288 valid_chunk_09 h10
  have h8 := valid_step 256 valid_chunk_08 h9
  have h7 := valid_step 224 valid_chunk_07 h8
  have h6 := valid_step 192 valid_chunk_06 h7
  have h5 := valid_step 160 valid_chunk_05 h6
  have h4 := valid_step 128 valid_chunk_04 h5
  have h3 := valid_step 96 valid_chunk_03 h4
  have h2 := valid_step 64 valid_chunk_02 h3
  have h1 := valid_step 32 valid_chunk_01 h2
  have h0 := valid_step 0 valid_chunk_00 h1
  simpa only [List.drop_zero] using h0

theorem certificate_validity : certificates.all validCertificate = true := by
  simpa only [certificates, List.all_map, Function.comp_def] using required_pairs_valid

end

#print axioms certificate_validity

end ConcreteGeometry213
