import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_20 :
    ((requiredPairs.drop 640).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_21 :
    ((requiredPairs.drop 672).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_22 :
    ((requiredPairs.drop 704).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_23 :
    ((requiredPairs.drop 736).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_24 :
    ((requiredPairs.drop 768).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_20
#print axioms valid_chunk_21
#print axioms valid_chunk_22
#print axioms valid_chunk_23
#print axioms valid_chunk_24
end ConcreteGeometry213
