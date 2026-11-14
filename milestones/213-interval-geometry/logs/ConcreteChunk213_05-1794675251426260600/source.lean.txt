import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_25 :
    ((requiredPairs.drop 800).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_26 :
    ((requiredPairs.drop 832).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_27 :
    ((requiredPairs.drop 864).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_28 :
    ((requiredPairs.drop 896).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_29 :
    ((requiredPairs.drop 928).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_25
#print axioms valid_chunk_26
#print axioms valid_chunk_27
#print axioms valid_chunk_28
#print axioms valid_chunk_29
end ConcreteGeometry213
