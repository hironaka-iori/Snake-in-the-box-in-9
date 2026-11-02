"""Stage the verified manifest without exceeding Windows argument limits."""
from pathlib import Path
import json,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
manifest=HERE/'data/file-manifest.json';rows=json.loads(manifest.read_text())['files']
names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
path=HERE/'build/stage-paths.nul';path.parent.mkdir(exist_ok=True)
path.write_bytes(b'\0'.join(n.encode('utf-8') for n in names)+b'\0')
subprocess.run(['git','-c','core.commitGraph=false','-c','core.safecrlf=false','add',
    '--pathspec-from-file='+str(path),'--pathspec-file-nul'],cwd=ROOT,check=True)
print('Staged',len(names),'owned paths')
