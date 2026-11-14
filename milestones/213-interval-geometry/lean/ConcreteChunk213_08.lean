import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_40 :
    ((requiredPairs.drop 1280).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_tail :
    (requiredPairs.drop 1312).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_40
#print axioms valid_tail
end ConcreteGeometry213
