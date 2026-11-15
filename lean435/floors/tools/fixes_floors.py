# Manual fixes for the floor port (module, old, new, count, reason); read by port_floors.py.
# Each must match exactly `count` times, or the port fails.
_RC5 = 'rcases (show {v} = 0 ∨ {v} = 1 ∨ {v} = 2 ∨ {v} = 3 ∨ {v} = 4 by {p}) with rfl | rfl | rfl | rfl | rfl'
_RC6 = 'rcases (show {v} = 0 ∨ {v} = 1 ∨ {v} = 2 ∨ {v} = 3 ∨ {v} = 4 ∨ {v} = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl'
_NOML = ('mathlib is not available in this environment (its dependency repositories cannot be '
         'downloaded); the module uses no mathlib declaration, only `interval_cases`, replaced below')
_IC = '`interval_cases` (mathlib) replaced by a core case split with the same goals in the same order'
FIXES = [
    ('CanonicalShareAdapter', 'import Mathlib.Tactic.IntervalCases\n', '', 1, _NOML),
    ('CanonicalShareAdapter', 'interval_cases i <;> simpa [broadBounds] using upper)',
     _RC5.format(v='i', p='omega') + ' <;> simpa [broadBounds] using upper)', 1, _IC),
    ('CriticalShareAdapter154', 'interval_cases i <;> simp [Nat.add_assoc,h1,h2,h3,h4,h5])',
     _RC5.format(v='i', p='first | omega | (simp at hi; omega)') + ' <;> simp [Nat.add_assoc,h1,h2,h3,h4,h5])', 2, _IC),
]
for _c in ('7300', '7304', '7306'):
    FIXES += [
        (f'Share{_c}.Compose', 'import Mathlib.Tactic\n', '', 1, _NOML),
        (f'Share{_c}.Geometry', 'import Mathlib.Tactic\n', '', 1, _NOML),
        (f'Share{_c}.Geometry', '      interval_cases j\n', '      ' + _RC6.format(v='j') + '\n', 1, _IC),
        (f'Share{_c}.Geometry', 'interval_cases i <;> simpa [bounds] using hu)',
         _RC5.format(v='i', p='omega') + ' <;> simpa [bounds] using hu)', 1, _IC),
        (f'Share{_c}.Reversal', 'interval_cases j <;> rfl)', _RC6.format(v='j') + ' <;> rfl)', 1, _IC),
    ]
# Fixes to branch modules after the port lead's port.py (applied to its output; modules the port
# lead's 86-module core stack does not contain).
FIXES += [
    ('WindowAutomatonBridge', 'simp only [List.length_cons, Nat.add_left_eq_self, List.length_eq_zero,',
     'simp only [List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff,', 1,
     '4.35 renames: `Nat.add_left_eq_self` -> `Nat.add_eq_right`, `List.length_eq_zero` -> `List.length_eq_zero_iff`'),
    ('WindowAutomatonBridge', 'rw [List.length_eq_zero, List.filter_eq_nil_iff] at h',
     'rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h', 1, 'same'),
]
for _n in ('150', '153'):
    FIXES.append((f'ReplayRawChunks{_n}', 'List.all_map, ', 'List.all_map, Function.comp_def, ', 1,
                  '`List.all_map` now produces `f ∘ g`; unfold the composition so `h` matches the goal'))
_W = ('`winOf` reduces through `Nat.xor`, which 4.35 core does not expose, so `simp` no longer '
      'evaluates `winOf [0,1,2,0,3,2]`; the window is rewritten first by a kernel evaluation')
FIXES += [
    ('ShareFromCore150', '  have href : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15 := by\n',
     '  have href : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15 := by\n'
     '    rw [show winOf [0,1,2,0,3,2] = [0,1,3,7,6,14,10] by decide +kernel,\n'
     '      show broadBounds = [(0,21),(0,21),(0,21),(0,21),(0,21)] from rfl]\n', 1,
     _W + '; likewise `simp only [broadBounds]` stops at `List.replicate 5 (0,21)`'),
    ('CriticalShareAdapter154', '      [(4,4),(0,4),(4,4),(0,5),(3,3)] 12 16 := by\n    simpa only',
     '      [(4,4),(0,4),(4,4),(0,5),(3,3)] 12 16 := by\n'
     '    rw [show winOf [0,1,2,0,3,2] = [0,1,3,7,6,14,10] by decide +kernel]\n    simpa only', 1, _W),
    ('DirectionWindowBridge7', '    CoverH T hkeys := by\n  simpa [coverHb] using h\n',
     '    CoverH T hkeys := by\n  simpa [coverHb, CoverH] using h\n', 1,
     '`simpa` no longer unfolds the `def` `CoverH` in the goal'),
]
FIXES.append(('DirectionWindowBridge6S', '    CoverH8 T hkeys := by\n  simpa [coverH8b] using h\n',
              '    CoverH8 T hkeys := by\n  simpa [coverH8b, CoverH8] using h\n', 1,
              '`simpa` no longer unfolds the `def` `CoverH8` in the goal'))
