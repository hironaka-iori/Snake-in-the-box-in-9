import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_00 :
    ((requiredPairs.drop 0).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_01 :
    ((requiredPairs.drop 32).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_02 :
    ((requiredPairs.drop 64).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_03 :
    ((requiredPairs.drop 96).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_04 :
    ((requiredPairs.drop 128).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_00
#print axioms valid_chunk_01
#print axioms valid_chunk_02
#print axioms valid_chunk_03
#print axioms valid_chunk_04
end ConcreteGeometry213
