"""Preserve proof bytes while applying the root text-file LF convention."""
from pathlib import Path
import hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
manifest=json.loads((H/'data/publication-manifest.json').read_text())
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
staged=subprocess.check_output(git+['diff','--cached','--name-only','-z'],cwd=R)
paths={p.decode() for p in staged.split(b'\0') if p}
expected=set(manifest['files'])|{(H/'data/publication-manifest.json').relative_to(R).as_posix()}
assert paths<=expected
subprocess.run(git+['restore','--staged','--']+sorted(paths),cwd=R,check=True)
changes=[]
for name in ['README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']:
    p=R/name;before=p.read_bytes();after=before.replace(b'\r\n',b'\n')
    p.write_bytes(after)
    changes.append(dict(path=name,before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(after).hexdigest()))
(H/'data/publication-repair.json').write_text(json.dumps(dict(
    reason='Initial exact-byte staging check rejected README line-ending conversion required by root attributes.',
    repair='Unstaged only manifest-owned paths; normalized the three Markdown status documents to LF. Preserved proof sources, plans, objects and receipts byte-for-byte.',
    whitespace='Use core.whitespace=cr-at-eol for preserved Windows research records.',changes=changes),indent=2)+'\n')
print('NORMALIZED_THREE_STATUS_DOCUMENTS')
