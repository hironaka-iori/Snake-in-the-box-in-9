import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_15 :
    ((requiredPairs.drop 480).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_16 :
    ((requiredPairs.drop 512).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_17 :
    ((requiredPairs.drop 544).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_18 :
    ((requiredPairs.drop 576).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_19 :
    ((requiredPairs.drop 608).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_15
#print axioms valid_chunk_16
#print axioms valid_chunk_17
#print axioms valid_chunk_18
#print axioms valid_chunk_19
end ConcreteGeometry213
