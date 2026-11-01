"""Read-only Git extraction of contributor interfaces for source comparison."""
from pathlib import Path
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
COMMIT='cd0c90fddf12170d735ee34fcc501e99c60632a6'
names=['UpperBound234','AggregateDirection7B234','AggregateDirection7Conditional',
 'DirectionWindowBridge7','DirectionWindowBridge7B234','DirectionWindowBridge6','WindowAutomaton7Defs',
 'WindowAutomaton7B234Sequence','WindowAutomaton6Defs','ShareBridge','AggregateWindowUnconditional']
rows=[]
for name in names:
    source='work/spectral/stronger/'+name+'.lean'
    r=subprocess.run(['git','show',COMMIT+':'+source],cwd=ROOT,capture_output=True)
    if r.returncode:
        rows.append(dict(path=source,error=r.stderr.decode(errors='replace')));continue
    dest=HERE/'upstream'/Path(source).name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(r.stdout)
    rows.append(dict(path=source,snapshot=str(dest.relative_to(HERE)),sha256=hashlib.sha256(r.stdout).hexdigest(),bytes=len(r.stdout)))
source='milestones/25-k7-234/lean/README.md'
r=subprocess.run(['git','show',COMMIT+':'+source],cwd=ROOT,capture_output=True,check=True)
dest=HERE/'upstream/Contributor-k7-README.md';dest.write_bytes(r.stdout)
rows.append(dict(path=source,snapshot=str(dest.relative_to(HERE)),sha256=hashlib.sha256(r.stdout).hexdigest(),bytes=len(r.stdout)))
(HERE/'data').mkdir(exist_ok=True)
(HERE/'data/contributor-sources.json').write_text(json.dumps(dict(commit=COMMIT,sources=rows,scope='Source inspection only. Extraction does not verify the contributor bound or its certificate dependency graph.'),indent=2)+'\n')
print([(r['path'],r.get('bytes',r.get('error'))) for r in rows])
