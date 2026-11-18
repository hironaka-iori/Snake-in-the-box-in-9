"""Per 8-direction shape: minimum over real bank-snake windows of W12 = sum_7 (24 alpha + share12)."""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import seeds as SD
from combined import exact, window_from_dirs
best = {}
for p, S in SD.bank_paths():
    for c, sel in SD.occurrences(p, S):
        w = window_from_dirs(list(c))
        if c in best and best[c][0] < 1200 and len(best[c]) > 3:
            pass
        A, SH = exact(w, sel, 12)
        v = 24 * sum(A) + sum(SH)
        if c not in best or v < best[c][0]:
            best[c] = (v, sum(A), sum(SH))
items = sorted(best.items(), key=lambda t: t[1][0])
print(len(items), 'shapes occur')
for c, v in items[:15]:
    print(c, v)
json.dump({','.join(map(str, c)): v for c, v in items}, open('data/real_shape_min.json', 'w'))
