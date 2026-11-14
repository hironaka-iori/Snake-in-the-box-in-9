import ConcreteRelations213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213
open IndexedCriterion206 Square209

private theorem map_certificate_pairs (xs : List (Nat × Nat)) :
    (xs.map makeCertificate).map (fun c => (c.1,c.2.1)) = xs := by
  simp only [List.map_map, Function.comp_def, certificate_pair,
    List.map_id_fun]
  exact List.map_id xs

section
attribute [local irreducible] requiredPairs makeCertificate

theorem certificate_coverage :
    certificates.map (fun c => (c.1,c.2.1)) = requiredPairs := by
  unfold certificates
  exact map_certificate_pairs requiredPairs

end

#print axioms certificate_coverage


end ConcreteGeometry213
