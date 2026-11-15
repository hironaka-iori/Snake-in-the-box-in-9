"""Align three generated Markdown files with their existing Git LF policy."""
from pathlib import Path
import json,hashlib,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
p=H/'data/publication-manifest.json';raw=p.read_bytes();m=json.loads(raw)
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
changed=subprocess.check_output(git+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0')
names={x.decode() for x in changed if x}
allowed=set(m['files'])|{str(p.relative_to(R)).replace('\\','/')}
assert names<=allowed
paths=sorted(allowed)
spec=b''.join((':(literal)'+name).encode()+b'\0' for name in paths)
subprocess.run(git+['restore','--staged','--pathspec-from-file=-','--pathspec-file-nul'],cwd=R,input=spec,check=True)
(H/'data/publication-manifest-initial.json').write_bytes(raw)
repairs={}
for name in ['README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']:
    q=R/name;before=q.read_bytes();after=before.replace(b'\r\n',b'\n')
    q.write_bytes(after)
    repairs[name]=dict(before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(after).hexdigest(),change='CRLF to LF only, matching existing .md text eol=lf attribute')
(H/'data/publication-repair.json').write_text(json.dumps(dict(reason='Exact-index verification detected Git newline normalization in generated Markdown. Preserve initial manifest; normalize only three generated files and recreate exact manifest.',repairs=repairs),indent=2)+'\n',encoding='utf-8',newline='\n')
p.unlink()
print('NORMALIZED_GENERATED_MARKDOWN; RECREATE_MANIFEST')
