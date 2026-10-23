"""Screen the next saved witness-table cycle; solver evidence only."""
import hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import plain,canonical
source=ROOT/'milestones/30-coarse-count-correction/data/selective-graph.json'
record=json.loads(source.read_text());run=record['runs'][-1];seen=set()
for e in run['cycle']:
    ds=canonical(e['directions'])
    if ds in seen:continue
    seen.add(ds);row=plain(dict(dirs=list(ds)),30)
    row.update(alpha=[[4,4]]*7,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256_lf=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest())
    p=HERE/f'data/next-all4-{len(seen)}.json';p.write_text(json.dumps(row,indent=2)+'\n')
    print(ds,row['status'],len(row['cycle_cuts']),flush=True)
