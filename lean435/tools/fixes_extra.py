# Manual fixes found while porting (module, old, new, count, reason); read by port.py.
FIXES = [
    ('LocalWindowBridge', "(CPerm.build_spec ds CPerm.id 0 hn hlt (by omega) (fun _ _ => Nat.zero_le _)).2 i hi\n  simpa using this\n",
     "(CPerm.build_spec ds CPerm.id 0 hn hlt (by omega) (fun _ _ => Nat.zero_le _)).2 i hi\n  simpa [mkPerm] using this\n", 1,
     '`simpa using this` no longer unfolds `mkPerm` (mkPerm_spec)'),
    ('LocalWindowBridge', "      · rw [← h]; simp)\n  simpa using h\n",
     "      · rw [← h]; simp)\n  simpa [cnt] using h\n", 1,
     '`simpa using h` no longer unfolds `cnt` (frame_deg_mid)'),
    ('LocalWindowBridge', "      · rw [if_neg h0, show j = m - 1 by omega]; simp)\n  simpa using h\n",
     "      · rw [if_neg h0, show j = m - 1 by omega]; simp)\n  simpa [cnt] using h\n", 1,
     'same (frame_deg_end)'),
    ('DirectionWindowBridge7', "    CoverH T hkeys := by\n  simpa [coverHb] using h\n",
     "    CoverH T hkeys := by\n  simpa [coverHb, CoverH] using h\n", 1,
     '`simpa using h` no longer unfolds the goal definition `CoverH`'),
    ('DirectionWindowBridge6S', "    CoverH8 T hkeys := by\n  simpa [coverH8b] using h\n",
     "    CoverH8 T hkeys := by\n  simpa [coverH8b, CoverH8] using h\n", 1,
     '`simpa using h` no longer unfolds the goal definition `CoverH8`'),
    ('SharedOuterSwitch', "simpa only [mirror,Finset.pair_comm h.y h.x] using hF",
     "simpa only [mirror,MissingAtNeighbor.mirror,Finset.pair_comm h.y h.x] using hF", 1,
     'simp no longer unfolds `MissingAtNeighbor.mirror` through the ambiguous `mirror`'),
    ('SharedFiniteClassification',
     "  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht\n",
     "  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht\n  simp only [sharedFiniteR] at hcount\n", 21,
     'simp unfolded `ordinaryGoodIndices` before `sharedFiniteR`, leaving a Classical decidability instance for the old '
     'predicate; 4.35 no longer matches `Finset.filter_insert` across that mismatch. Unfolding `sharedFiniteR` first restores it'),
]

# K7R34C7W16 window-automaton chain (older line, ported from ~/l435/k7/rkroot).
FIXES += [
    ('WindowAutomatonLoop', "  rw [Nat.testBit_to_div_mod, Nat.and_one_is_mod,",
     "  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod,", 1,
     'core removed `Nat.testBit_to_div_mod`; `testBit_eq_decide_div_mod_eq` is the same statement'),
    ('WindowAutomatonLit', "\nunsafe def elabNatLitImpl : TermElab :=", "\nmeta unsafe def elabNatLitImpl : TermElab :=", 1,
     'the `nat_lit%` elaborator runs at compile time: the module system requires it to be `meta`'),
    ('WindowAutomatonLit', "\nopaque elabNatLitCore : TermElab", "\nmeta opaque elabNatLitCore : TermElab", 1, 'same'),
    ('WindowAutomatonLit', "\ndef elabNatLit : TermElab := elabNatLitCore", "\nmeta def elabNatLit : TermElab := elabNatLitCore", 1,
     'same (`[term_elab]` needs a `meta` declaration)'),
    ('WindowAutomatonK7R34C7W16Base', "\nimport WindowAutomatonLit16\n",
     "\nimport WindowAutomatonLit16\nmeta import WindowAutomatonLit\n", 1,
     '`nat_lit% ofB64 ..` runs imported code while elaborating: it needs a `meta import` (kept in the header by port.py)'),
    ('WindowAutomatonK7R34C7W16Base', "  have h2 := congrArg (fun X => digit16 X (y % 512)) h1\n  simp only at h2\n",
     "  have h2 := congrArg (fun X => digit16 X (y % 512)) h1\n  try simp only at h2\n", 1,
     '`congrArg (fun X => ..) h1` is now beta-reduced, so `simp only` made no progress (an error)'),
    ('WindowAutomatonK7R34C7W16Spec', "(fun l hl' => by dsimp only; have := hb1 (l % 262144)",
     "(fun l hl' => by (try dsimp only); have := hb1 (l % 262144)", 1,
     'the hypotheses of `swarOK16_spec` are now stated beta-reduced, so `dsimp only` made no progress (an error)'),
    ('WindowAutomatonK7R34C7W16Spec', "    (fun l hl' => by\n      dsimp only\n", "    (fun l hl' => by\n      try dsimp only\n", 1,
     'same'),
    ('WindowAutomatonK7R34C7W16Tab', "\nimport WindowAutomatonK7R34C7W16Base\n",
     "\nimport WindowAutomatonK7R34C7W16Base\nmeta import WindowAutomatonLit\n", 1,
     '`nat_lit% ofGaps ..` runs imported code while elaborating: it needs a `meta import` (kept in the header by port.py)'),
]
FIXES += [
    (m, "  rw [Nat.testBit_to_div_mod, Bool.eq_iff_iff,", "  rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff,", 1,
     'core removed `Nat.testBit_to_div_mod`; `testBit_eq_decide_div_mod_eq` is the same statement')
    for m in ('WindowAutomatonSwar', 'WindowAutomatonSwar16')
]
FIXES += [
    ('WindowAutomatonCode', "      have := congrArg (· / 8 ^ l'.length) e\n      simp only at this\n",
     "      have := congrArg (· / 8 ^ l'.length) e\n      try simp only at this\n", 1,
     '`congrArg (fun z => ..) e` is now beta-reduced, so `simp only` made no progress (an error)'),
]
FIXES += [
    (m, "    have h2 := congrArg (fun X => %s X l) h1\n    simp only at h2\n" % d,
     "    have h2 := congrArg (fun X => %s X l) h1\n    try simp only at h2\n" % d, 1,
     '`congrArg (fun X => ..) h1` is now beta-reduced, so `simp only` made no progress (an error)')
    for (m, d) in (('WindowAutomatonConsD', 'digit'), ('WindowAutomatonConsD16', 'digit16'))
]
FIXES += [
    ('WindowAutomatonRGS', "(c.drop j) (by simp [hc]; omega) hrest", "(c.drop j) (by simp [hc] <;> omega) hrest", 1,
     '`simp [hc]` now closes the length goal itself, so the following `omega` had no goal (an error)'),
]
FIXES += [
    (f'WindowAutomatonK7R34C7W16Pot{i}', "\nimport WindowAutomatonK7R34C7W16Base\n",
     "\nimport WindowAutomatonK7R34C7W16Base\nmeta import WindowAutomatonK7R34C7W16Base\n", 1,
     '`nat_lit% trans16/spreadBlocks16/ofB64 ..` (and `repBK..`) run imported code while elaborating: `meta import`')
    for i in range(33)
]
