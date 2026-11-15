# R6 renames (pattern, replacement, reason), mathlib/core of the 4.19 project -> v4.35.0; read by port.py.
RENAMES = [
    (r'\bFinset\.(\w*?)not_mem', r'Finset.\1notMem', 'mathlib renamed `not_mem` to `notMem` (Finset lemmas)'),
    (r'\bNat\.add_left_eq_self\b', 'Nat.add_eq_right', 'renamed (a + b = b ↔ a = 0)'),
    (r'\bList\.length_eq_zero\b', 'List.length_eq_zero_iff', 'renamed'),
    (r'\bFinset\.filter_card_add_filter_neg_card_eq_card\b', 'Finset.card_filter_add_card_filter_not', 'renamed'),
    (r'(?m)^(\s*)dsimp only at (\w+)\s*$', r'\1try dsimp only at \2',
     '`congrArg (fun z => ..) he` is now beta-reduced already: `dsimp only` made no progress (error)'),
    (r'(f k=localAlpha p ⟨k,hk⟩ :=) by simp \[f,hk\]', r'\1 dif_pos hk',
     'simp now rewrites the `dite` condition `k<m+1` to `k≤m` before using `hk`'),
]
