import ReplayTools153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayRawChunks153
theorem chunks_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow153.cnf = true) :
    Snake9.LocalWindow.ShareWindow153.raw0.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw1.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw2.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw3.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw4.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw5.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw6.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw7.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw8.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw9.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw10.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw11.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw12.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw13.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw14.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw15.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw16.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw17.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw18.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw19.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw20.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw21.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw22.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw23.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw24.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw25.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw26.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw27.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw28.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw29.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw30.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw31.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw32.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw33.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw34.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw35.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw36.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw37.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw38.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw39.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw40.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw41.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw42.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw43.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw44.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw45.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw46.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw47.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw48.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw49.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw50.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw51.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw52.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw53.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw54.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw55.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw56.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw57.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw58.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw59.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw60.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw61.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw62.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw63.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw64.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw65.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw66.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw67.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw68.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw69.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw70.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw71.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw72.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw73.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw74.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw75.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw76.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw77.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw78.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw79.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw80.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw81.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw82.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw83.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw84.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw85.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw86.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw87.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw88.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw89.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw90.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw91.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow153.raw92.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true := by
  simpa only [Snake9.LocalWindow.ShareWindow153.cnf, Snake9.LocalWindow.cnfTrue, List.all_map, Snake9.LocalWindow.ShareWindow153.raw,
    List.all_append, Bool.and_eq_true, List.all_nil, and_true, and_assoc] using h
#print axioms chunks_true
end Snake9.ReplayRawChunks153
