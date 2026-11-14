import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_30 :
    ((requiredPairs.drop 960).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_31 :
    ((requiredPairs.drop 992).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_32 :
    ((requiredPairs.drop 1024).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_33 :
    ((requiredPairs.drop 1056).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_34 :
    ((requiredPairs.drop 1088).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_30
#print axioms valid_chunk_31
#print axioms valid_chunk_32
#print axioms valid_chunk_33
#print axioms valid_chunk_34
end ConcreteGeometry213
