import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_33 :
    ((requiredPairs.drop 1056).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_33
end ConcreteGeometry213
