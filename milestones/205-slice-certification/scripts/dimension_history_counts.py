"""Apply the written component count to the pinned lower-dimensional seeds."""
from pathlib import Path
from collections import Counter
import hashlib,itertools,json
H=Path(__file__).resolve().parents[1];source=H/'data/lower-dimensional-input.json';inputs=json.loads(source.read_bytes());results=[]
for dim in (6,7,8):
 vertices=inputs[str(dim)]['vertices'];records=[]
 for a,b in itertools.combinations(range(dim),2):
  mask=((1<<dim)-1)^((1<<a)|(1<<b));counts=[]
  for parity in (0,1):
   active={x&mask for x in vertices if (((x>>a)^(x>>b))&1)==parity};unseen=set(active);components=[]
   while unseen:
    root=min(unseen);unseen.remove(root);queue=[root]
    for x in queue:
     for k in range(dim):
      y=x^(1<<k)
      if y in unseen:unseen.remove(y);queue.append(y)
    components.append(sorted(queue))
   counts.append(components)
  c=[len(x) for x in counts];r=sum(x>0 for x in c)
  records.append(dict(coordinates=[a,b],component_counts=c,components=counts,ordered_targets=2**(1+sum(c)),block_isometry_classes=2**(sum(c)-r)))
 histogram=Counter(str(x['block_isometry_classes']) for x in records)
 results.append(dict(dimension=dim,edges=len(vertices)-1,pairs=len(records),restricted_class_histogram=dict(histogram),records=records))
out=dict(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),results=results,scope='Native component counts on one fixed seed per dimension. Target counts use the written theorem; restricted block-isometry classes can merge under full-cube isometries or reversal.')
(H/'data/dimension-history-counts.json').write_text(json.dumps(out,indent=2)+'\n')
for r in results:print('Q',r['dimension'],'edges',r['edges'],'pairs',r['pairs'],'restricted class histogram',r['restricted_class_histogram'])
