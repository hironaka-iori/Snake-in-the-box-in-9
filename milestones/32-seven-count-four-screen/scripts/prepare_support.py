"""Pin the existing direction-normalization support and start an isolated build."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
names=['WindowAutomatonDefs','WindowAutomatonData','WindowAutomatonLemmas','WindowAutomatonSequence','WindowAutomatonBridge','LocalWindowDirModel','LocalWindowDirKeys','LocalWindowDirBridge','DirectionWindowBridge']
records=[]
for name in names:
    source=ROOT/('work/final_lean' if name.startswith('LocalWindowDir') else 'work/spectral/stronger')/(name+'.lean')
    raw=source.read_bytes();(HERE/'upstream'/(name+'.lean')).write_bytes(raw)
    records.append(dict(path=str(source.relative_to(ROOT)).replace('\\','/'),sha256_lf=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest()))
(HERE/'data/normalization-support.json').write_text(json.dumps(records,indent=2)+'\n')
print('Pinned nine normalization support modules.')
