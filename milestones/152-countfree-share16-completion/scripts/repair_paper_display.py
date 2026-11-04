"""Close a pre-existing display exposed by the now-working preview compiler."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
raw=paper.read_bytes();assert raw==editor.read_bytes()
sha=lambda b:hashlib.sha256(b).hexdigest()
revpath=H/'data/paper-revision.json';rev=json.loads(revpath.read_text())
assert sha(raw)==rev['source_sha256_after']=='36cc6030725b054a25827aed10d1edc36dbdbc719ecb9abd4e398a8e9304ea16'
before='\\end{aligned}\nThe denominator is positive and $65968=133\\cdot496$.'
after='\\end{aligned}\n\\]\nThe denominator is positive and $65968=133\\cdot496$.'
text=raw.decode('utf-8');assert text.count(before)==1
out=text.replace(before,after).encode('utf-8')
(H/'audit/paper-revision-before-compile-repair.json').write_bytes(revpath.read_bytes())
(H/'audit/paper-before-compile-repair.tex.txt').write_bytes(raw)
rev['prose_replacements'].append(dict(before=before,after=after))
rev['source_sha256_after']=sha(out)
rev['compiler_repair']='Added the missing closing display delimiter after an existing aligned calculation; mathematical content unchanged.'
paper.write_bytes(out);editor.write_bytes(out)
revpath.write_text(json.dumps(rev,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status='REPAIRED_MISSING_DISPLAY_DELIMITER',paper_sha256=sha(out))))
