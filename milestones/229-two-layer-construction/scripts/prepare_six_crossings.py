"""Prepare the same retained-index construction with six total crossings."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
p=H/'scripts/joint_boundary.py';s=p.read_text(encoding='utf-8')
start=s.index("closure=json.loads(");end=s.index("source=H/'data'",start)
s=s[:start]+'assert a.width==46\n'+s[end:]
start=s.index('    selectors=[]');end=s.index("    model.add(sum(all_cross_edges)",start)
s=s[:start]+s[end:]
old="for row in raw['contexts']:\n"
assert s.count(old)==1
s=s.replace(old,old+"    row=dict(row);row['replacement_crossings']+=2\n",1)
s=s.replace('==4\n','==6\n')
old='A boundary-change cut uses the complete native45exclusion; zero-face shortages impose necessary crossing minima. The final snake hasfour bit8crossings.'
assert old in s
s=s.replace(old,'No boundary-change cut or smaller-width exclusion is assumed. Zero-face shortages impose necessary crossing minima. The final snake has six bit8crossings; the original fixed-crossing count is preserved, so each prepared replacement budget is increased by two.')
out=H/'scripts/joint_six.py';assert not out.exists();out.write_text(s,encoding='utf-8')
p=H/'scripts/run_boundary.py';r=p.read_text(encoding='utf-8').replace('joint_boundary.py','joint_six.py').replace(", H/'data/coverage45.json'",'')
(H/'scripts/run_six.py').write_text(r,encoding='utf-8')
raw=json.loads((H/'data/regions46.json').read_bytes())
ids=[c['id'] for c in raw['contexts'] if c['status']=='PENDING']
j=dict(status='PREPARED_UNEXECUTED',width=46,total_crossings=6,ids=ids,static_exclusions=[c['id'] for c in raw['contexts'] if c['status']=='STATIC_EXCLUDED'],pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [H/'data/regions46.json',H/'scripts/joint_six.py',H/'scripts/run_six.py',Path(__file__)]},scope='Same seed, append24, two length-preserving width46blocks, but six total bit8crossings. Domains and initial geometry are crossing-independent. No four-crossing boundary cut or prior-width exclusion is carried into this search. Every witness requires full193vertex inducedness and exactsixcrossing audit.')
(H/'data/six-crossing-plan.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
print('PREPARED_SIX_CROSSING_QUERIES',len(ids))
