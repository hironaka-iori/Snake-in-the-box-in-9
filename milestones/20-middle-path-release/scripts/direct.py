"""Direct 196-edge search near the new two-arm seed, with no frozen middle."""
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work'))
sys.path.insert(0,str(ROOT/'milestones/19-coordinate-face-repair/scripts'))
from neighborhood_search import solve
from search_faces import sha

source=ROOT/'milestones/19-coordinate-face-repair/data/two-arm-seed186.json'
path=json.loads(source.read_text())['path_vertices']
result=solve(9,196,path,64,120)
result.update(source_sha256_lf=sha(source),script_sha256_lf=sha(Path(__file__)),
              model_sha256_lf=sha(ROOT/'work/neighborhood_search.py'),
              scope='No middle segment is frozen. At least 123 of the 187 seed vertices are retained; failure is not a global bound.')
(HERE/'data').mkdir(parents=True,exist_ok=True)
(HERE/'data/direct196.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:result[k] for k in ('status','target_edges','elapsed_seconds')}),flush=True)
