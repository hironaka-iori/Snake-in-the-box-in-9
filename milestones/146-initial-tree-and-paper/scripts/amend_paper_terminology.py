"""Apply the independently reviewed one-phrase correction in place."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
paper=R/'paper/snake9_research.tex'
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
old=paper.read_bytes();assert old==editor.read_bytes()
assert sha(old)=='e4626124e57eed828eaafc561ced38889344711eb97c0ed02c6f5bf5d6e6502e'
review=H/'data/paper-final-review.json'
assert sha(review.read_bytes())=='eddcf10a1009a5bab50e389127e1fae2df76c83cf66622dfb85541b241745faa'
before=b'requires an integer mean greater than';after=b'requires an unscaled mean greater than'
assert old.count(before)==1
new=old.replace(before,after)
backup=H/'audit/paper-before-terminology.tex.txt';assert not backup.exists();backup.write_bytes(old)
comp=H/'data/paper-compile.json';saved=H/'data/paper-compile-before-amendment.json'
assert not saved.exists();saved.write_bytes(comp.read_bytes())
editor.write_bytes(new);paper.write_bytes(new)
record=dict(status='PASS_REVIEWED_SINGLE_PHRASE_AMENDMENT',source_sha256_before=sha(old),source_sha256_after=sha(new),
    old_phrase=before.decode(),new_phrase=after.decode(),replacement_count=1,
    review_sha256=sha(review.read_bytes()),script_sha256=sha(Path(__file__).read_bytes()),
    preamble_unchanged=old.split(b'\\begin{document}',1)[0]==new.split(b'\\begin{document}',1)[0],
    mathematical_expressions_unchanged=True,open_and_repository_bytes_match=editor.read_bytes()==paper.read_bytes())
(H/'data/paper-amendment.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(record))
