import ReplayTools150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayRawChunks150
theorem chunks_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow150.cnf = true) :
    Snake9.LocalWindow.ShareWindow150.raw0.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw1.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw2.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw3.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw4.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw5.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw6.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw7.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw8.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw9.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw10.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw11.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw12.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw13.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw14.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw15.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw16.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw17.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw18.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw19.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw20.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw21.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw22.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw23.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw24.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw25.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw26.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw27.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw28.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw29.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw30.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw31.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw32.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw33.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw34.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw35.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw36.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw37.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw38.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw39.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw40.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw41.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw42.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw43.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw44.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw45.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw46.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw47.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw48.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw49.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw50.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw51.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw52.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw53.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw54.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw55.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw56.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw57.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw58.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw59.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw60.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw61.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw62.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw63.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw64.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw65.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw66.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw67.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw68.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw69.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw70.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw71.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw72.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw73.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw74.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw75.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw76.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw77.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw78.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw79.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw80.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw81.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw82.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw83.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw84.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw85.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw86.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw87.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw88.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw89.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw90.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw91.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw92.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw93.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw94.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw95.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw96.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw97.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw98.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw99.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw100.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw101.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw102.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw103.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw104.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw105.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true ∧
    Snake9.LocalWindow.ShareWindow150.raw106.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true := by
  simpa only [Snake9.LocalWindow.ShareWindow150.cnf, Snake9.LocalWindow.cnfTrue, List.all_map, Snake9.LocalWindow.ShareWindow150.raw,
    List.all_append, Bool.and_eq_true, List.all_nil, and_true, and_assoc] using h
#print axioms chunks_true
end Snake9.ReplayRawChunks150
