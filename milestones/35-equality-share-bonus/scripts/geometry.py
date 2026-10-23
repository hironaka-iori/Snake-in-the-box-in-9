"""Independent enumeration of the three forced squares and share denominators."""
import itertools,json
from pathlib import Path
HERE=Path(__file__).resolve().parents[1]

def inspect(dirs):
 w=[0]
 for d in dirs:w.append(w[-1]^(1<<d))
 selected=set(w)
 forbidden={v^(1<<a) for v in w[1:-1] for a in range(9)}-selected
 assert all(sum((v^(1<<a)) in selected for a in range(9))==2 for v in w[1:-1])
 rows=[];squares=set()
 for c in (w[1],w[6]):
  for h in range(9):
   q=c^(1<<h)
   sq=[tuple(sorted((q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)))) for a,b in itertools.combinations(range(9),2)
       if {q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}<=forbidden]
   if not sq:continue
   absent_neighbors=sorted(q^(1<<a) for a in range(9) if (q^(1<<a)) in forbidden)
   maximum=9-len(absent_neighbors);assert maximum>0
   rows.append(dict(centre=c,neighbor=q,empty_squares=len(sq),absent_neighbors=absent_neighbors,degree_upper=maximum,share_lower=12*len(sq)//maximum))
   squares.update(sq)
 assert sum(r['share_lower'] for r in rows)==12
 return dict(dirs=dirs,window=w,forced_absent=sorted(forbidden),squares=sorted(squares),rows=rows,share_lower=12)

if __name__=='__main__':
 rows=[inspect(d) for d in ([0,1,2,3,4,1,5],[0,1,2,3,4,1,0])]
 (HERE/'data/geometry.json').write_text(json.dumps(rows,indent=2)+'\n')
 print('Both patterns: three empty squares; share contributions 2,4,4,2.')
