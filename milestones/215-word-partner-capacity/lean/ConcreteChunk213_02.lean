import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_10 :
    ((requiredPairs.drop 320).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_11 :
    ((requiredPairs.drop 352).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_12 :
    ((requiredPairs.drop 384).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_13 :
    ((requiredPairs.drop 416).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_14 :
    ((requiredPairs.drop 448).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_10
#print axioms valid_chunk_11
#print axioms valid_chunk_12
#print axioms valid_chunk_13
#print axioms valid_chunk_14
end ConcreteGeometry213
