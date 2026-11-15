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
     _RC5.format(v='i', p='simp at hi; omega') + ' <;> simp [Nat.add_assoc,h1,h2,h3,h4,h5])', 2, _IC),
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
