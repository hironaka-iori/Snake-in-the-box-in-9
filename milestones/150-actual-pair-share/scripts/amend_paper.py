"""Make the existing verification paragraph refer to all three pending targets."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
raw=paper.read_bytes();assert raw==editor.read_bytes()
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(raw)=='53f6565e04cbe852ce1949269e4f6802b84ea535987462ba64e6b4f619f8eec7'
before='without completing either\nlocal share theorem'
after='without completing these\nlocal share theorems'
text=raw.decode('utf-8');assert text.count(before)==1
out=text.replace(before,after).encode('utf-8');paper.write_bytes(out);editor.write_bytes(out)
p=H/'data/paper-revision.json';j=json.loads(p.read_text(encoding='utf-8'))
assert j['source_sha256_after']==sha(raw)
j.update(source_sha256_before_wording_amendment=sha(raw),source_sha256_after=sha(out),
    prose_replacements=[dict(before=before,after=after)])
p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
old=H/'data/paper-compile.json';saved=H/'audit/paper-compile-before-wording.json'
assert not saved.exists();saved.write_bytes(old.read_bytes())
print(json.dumps(dict(status='PASS_THREE_TARGET_WORDING_AMENDMENT',paper_sha256=sha(out))))
