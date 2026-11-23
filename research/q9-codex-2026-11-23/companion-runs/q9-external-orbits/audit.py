from pathlib import Path
from collections import Counter
from setup import read,flaws,check
import json,itertools,sys
r=Path(__file__).resolve().parent
orig=read(r/'walks.pts');summary={'input_rows':len(orig),'chord_index_separations':dict(Counter(b-a for q in orig for a,b in flaws(q)))}
assert all(len(p)==193 and len(flaws(p))==1 for p in orig)
for prefix in ['ctrl','initial','wide','quick','barrier','csp_ctrl','cut_ctrl','cut','cutlong']:
 log=r/(prefix+'.log');out=r/(prefix+'.out')
 if not log.exists() or not out.exists() or not log.stat().st_size:continue
 positive=[]
 for z in read(out):
  i,rep,*p=z;check(p,191 if prefix.endswith('ctrl') or prefix=='ctrl' else 192);positive.append(i)
 summary[prefix]={'log':log.read_text().strip(),'verified_witnesses':len(positive),'rows':positive}
summary["common_four_choice_encoding"]={"native":(r/"cross.log").read_text().strip(),"independent_sat":(r/"cross-sat.log").read_text().strip()}
print(summary);(r/'audit.json').write_text(json.dumps(summary,indent=2)+'\n')

