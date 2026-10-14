import json
from pathlib import Path
from neighborhood_search import solve
# Root 0 is an interior vertex in the known 4-edge extension; free endpoints matter.
seed=[1,0,2]
r=solve(3,4,seed,0,5)
assert r['status']=='OPTIMAL' and 'witness' in r
assert 0 not in [r['witness'][0],r['witness'][-1]]
s=solve(3,5,seed,0,5)
assert s['status']=='INFEASIBLE'
Path('outputs/neighborhood_controls.json').write_text(json.dumps([r,s],indent=2))
print(json.dumps([r,s],indent=2))
