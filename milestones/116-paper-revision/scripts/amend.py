"""Apply the review's clause-count precision correction to both saved sources."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
raw=paper.read_bytes();assert raw==editor.read_bytes()
before=b'proof uses 5067 input clauses, 287753 deductions and 16816989 antecedent'
after=b'proof uses 5067 of its 5114 input clauses, 287753 deductions and 16816989 antecedent'
assert raw.count(before)==1
new=raw.replace(before,after);paper.write_bytes(new);editor.write_bytes(new)
path=HERE/'data/revision.json';r=json.loads(path.read_text())
r['intermediate_source_sha256']=hashlib.sha256(raw).hexdigest()
r['paper_sha256']=hashlib.sha256(new).hexdigest()
r['review_correction']='Distinguish 5114 supplied clauses from the 5067 clauses used in the selected proof.'
path.write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print(r['paper_sha256'])
