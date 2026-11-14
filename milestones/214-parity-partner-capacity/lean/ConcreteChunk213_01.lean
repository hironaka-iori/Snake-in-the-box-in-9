import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

theorem valid_chunk_05 :
    ((requiredPairs.drop 160).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_06 :
    ((requiredPairs.drop 192).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_07 :
    ((requiredPairs.drop 224).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_08 :
    ((requiredPairs.drop 256).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

theorem valid_chunk_09 :
    ((requiredPairs.drop 288).take 32).all
      (fun xy => validCertificate (makeCertificate xy)) = true := by
  decide +kernel

#print axioms valid_chunk_05
#print axioms valid_chunk_06
#print axioms valid_chunk_07
#print axioms valid_chunk_08
#print axioms valid_chunk_09
end ConcreteGeometry213
