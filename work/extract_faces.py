import json
from pathlib import Path
b = json.loads(Path('work/bank9.json').read_text())
best = (0, None)
for row in b:
    for k in range(9):
        actions = row['transition_sequence']
        cuts = [-1] + [i for i,x in enumerate(actions) if x == k] + [len(actions)]
        for lo,hi in zip(cuts,cuts[1:]):
            if hi-lo-1 > best[0]:
                best = hi-lo-1, {'coordinate':k, 'vertices':row['vertex_sequence'][lo+1:hi+1]}
print(json.dumps(best))
Path('work/longest_face.json').write_text(json.dumps(best))
