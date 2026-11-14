import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_35 :
    ((requiredPairs.drop 1120).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_36 :
    ((requiredPairs.drop 1152).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_37 :
    ((requiredPairs.drop 1184).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_38 :
    ((requiredPairs.drop 1216).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_39 :
    ((requiredPairs.drop 1248).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_35
#print axioms valid_chunk_36
#print axioms valid_chunk_37
#print axioms valid_chunk_38
#print axioms valid_chunk_39
end ConcreteGeometry213
