"""Verify the exact Q9 adjacency inverse by integer matrix entries."""
from pathlib import Path
import hashlib
import json
from collections import Counter

H = Path(__file__).resolve().parents[1]
dest = H / 'data/inverse-audit.json'
assert not dest.exists()
weights = [0, 35, 0, -10, 0, 8, 0, -16, 0, 128]
counts = Counter()
digest = hashlib.sha256()
for a in range(512):
    row = []
    for b in range(512):
        value = sum(weights[(a ^ (b ^ (1 << j))).bit_count()] for j in range(9))
        assert value == (315 if a == b else 0), (a, b, value)
        counts[value] += 1
        row.append(value)
    digest.update((','.join(map(str, row)) + '\n').encode('ascii'))
out = dict(status='PASS_EXACT_Q9_INVERSE', vertices=512, entries=512*512,
           distance_weights=weights, product_scale=315, entry_counts=dict(counts),
           matrix_product_sha256=digest.hexdigest(),
           source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           scope='Exact integer verification of K A = 315 I on the full labelled Q9; A is cube adjacency and K(a,b) is the displayed distance weight. No solver or random sampling.',
           limitations='This finite calculation is separate from the Lean general linear-combination lemma and the written cube distance-count proof. It gives no new snake or global upper bound.')
dest.write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(out, indent=2))
