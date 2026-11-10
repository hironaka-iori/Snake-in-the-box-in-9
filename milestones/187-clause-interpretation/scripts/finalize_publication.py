from pathlib import Path
import json,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/187-clause-interpretation';D=Path('D:/Codex/2026-10-13/new-chat/outputs')
receipts=json.loads(Path('D:/Codex/2026-10-13/new-chat/work/round187_compile_receipts.json').read_text())
for name in ['frontier','main']:
    assert not receipts[name]['isError']
    assert json.loads(receipts[name]['content'][0]['text'])['kind']=='success'
docs={}
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    a=(D/name).read_bytes();b=(R/'paper'/name).read_bytes();assert a==b
    docs[name]={'sha256':hashlib.sha256(a).hexdigest(),'bytes':len(a)}
(H/'data/latex-compilation.json').write_text(json.dumps({'receipts':receipts,'documents':docs,'scope':'Both existing sources compiled successfully; no full visual or manuscript-wide review claimed.'},indent=2)+'\n')
(H/'scripts/finalize_publication.py').write_bytes(Path(__file__).read_bytes())
p=H/'README.md';s=p.read_text();s+='\nBoth existing LaTeX sources compiled successfully with the desktop compiler. See data/latex-compilation.json. The initial stale-project responses are retained beside the successful retries.\n'
s+='\nThe first Combined187 attempt compiled with exit code zero but failed the report-count audit because a comment contained the report-command text. Removing that comment text made the second audit pass; both records are retained.\n'
p.write_text(s,encoding='utf-8',newline='\n')
print('Saved successful compilation receipts and matching document hashes.')
