"""Correct stale manuscript pointers in the current repository introductions."""
from pathlib import Path
import hashlib, json, re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
record=HERE/'data/document-pointer-correction.json';assert not record.exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
source=ROOT/'milestones/106-paper-revision/data/checkpoint.json'
c=json.loads(source.read_text(encoding='utf-8-sig'))
assert c['paper_revision']==106 and c['named_definitions']==1
assert sha((ROOT/'paper/snake9_research.tex').read_bytes())==c['paper_sha256']
replacement='Current manuscript revision: [milestone 106](milestones/106-paper-revision/README.md). The paper incorporates the arguments through milestone 105 and retains one named definition, for the problem itself. All 13 printed snakes pass 118,673 vertex-pair checks. Authors, hyperlink settings and appendices are preserved. Source checks pass; the built-in compiler failed before TeX processing, so no current PDF or visual layout is verified. The next full revision is 116.'
rows=[]
for name in ['README.md','COLLABORATION.md','milestones/README.md']:
    p=ROOT/name;before=p.read_bytes();text=before.decode('utf-8')
    if name=='milestones/README.md':
        old='The manuscript is at revision 86. Source and witness checks pass; the app compiler cannot start.'
        assert old in text
        text=text.replace(old,'The manuscript is at revision 106; the next full revision is 116. Source and witness checks pass; the built-in compiler failed before TeX processing.')
    else:
        text,n=re.subn(r'^Current manuscript revision:.*$',replacement,text,count=1,flags=re.M);assert n==1
    p.write_bytes(text.encode('utf-8'))
    rows.append(dict(path=name,before_sha256=sha(before),after_sha256=sha(p.read_bytes())))
record.write_text(json.dumps(dict(status='CURRENT_MANUSCRIPT_POINTERS_CORRECTED',files=rows,
    source=source.relative_to(ROOT).as_posix(),source_sha256=sha(source.read_bytes()),
    scope='Repository introductions only; no paper or proof source changed.'),indent=2)+'\n',encoding='utf-8')
print('Corrected three current manuscript pointers to revision106')
