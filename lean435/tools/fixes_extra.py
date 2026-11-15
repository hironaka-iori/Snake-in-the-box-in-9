# Manual fixes found while porting (module, old, new, count, reason); read by port.py.
FIXES = [
    ('LocalWindowBridge', "      · rw [← h]; simp)\n  simpa using h\n",
     "      · rw [← h]; simp)\n  simpa [cnt] using h\n", 1,
     '`simpa using h` no longer unfolds `cnt` (frame_deg_mid)'),
    ('LocalWindowBridge', "      · rw [if_neg h0, show j = m - 1 by omega]; simp)\n  simpa using h\n",
     "      · rw [if_neg h0, show j = m - 1 by omega]; simp)\n  simpa [cnt] using h\n", 1,
     'same (frame_deg_end)'),
]
