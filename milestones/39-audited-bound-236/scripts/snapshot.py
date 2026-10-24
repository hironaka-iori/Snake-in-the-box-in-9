"""Pin the contributor's proof interfaces and audit receipts without merging its paper."""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[3]; HERE=Path(__file__).resolve().parents[1]
COMMIT='7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b'
names=['UpperBound236','AggregateDirection236Conditional','AggregateDirection236Unconditional',
       'WindowAutomaton5R4Data','WindowAutomaton5R4Table','WindowAutomaton5R4Sequence',
       'DirectionWindowBridge5R4']
paths=['work/spectral/stronger/'+n+'.lean' for n in names]
paths+=['work/final_lean/'+n+'.lean' for n in ['LocalWindowDirKeysR4','LocalWindowDirUnsatR4','LocalWindowDirSatR4']]
paths+=['outputs/upper-bound-236-'+n+'-linux.log' for n in ['audit','replay']]
records=[]
for p in paths:
 data=subprocess.check_output(['git','show',COMMIT+':'+p],cwd=ROOT)
 dest=HERE/'upstream'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 records.append(dict(path=p,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
part=(HERE/'upstream/work/final_lean/LocalWindowDirKeysR4.lean').read_text().split('def dirKeysR4 :')[1].split(']\n')[0]
keys=[[[int(x) for x in re.findall(r'\d+',a)],[int(x) for x in re.findall(r'\d+',b)]] for a,b in re.findall(r'\(\[([^]]+)\], \[([^]]+)\]\)',part)]
assert len(keys)==732 and len({str(k) for k in keys})==732
(HERE/'data').mkdir(exist_ok=True)
(HERE/'data/exclusion-catalogue.json').write_text(json.dumps(keys,separators=(',',':'))+'\n')
(HERE/'data/upstream-manifest.json').write_text(json.dumps(dict(commit=COMMIT,files=records,scope='Selected proof interfaces and recorded Linux audits. Complete dependency sources and replay generators remain at the pinned upstream commit; no local full rebuild is claimed.'),indent=2)+'\n')
print('Pinned',len(records),'files and',len(keys),'unique exclusions at',COMMIT)
