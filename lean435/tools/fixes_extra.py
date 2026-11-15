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
]
