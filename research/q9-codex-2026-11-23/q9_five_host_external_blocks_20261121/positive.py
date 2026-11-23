from pathlib import Path
import sys,json
from itertools import combinations
D=Path(__file__).resolve().parent
data=json.loads((D/'seeds.json').read_text())
for row,g in enumerate(data):
    p=g['path'];S=set(p);best=None
    for axes in combinations(range(9),4):
        m=sum(1<<d for d in axes)
        for base in sorted({x&~m for x in p}):
            block={x for x in range(512) if x&~m==base}
            deleted=S&block
            if 6<=len(deleted)<=9:
                spread=max(map(p.index,deleted))-min(map(p.index,deleted))
                if best is None or spread>best[0]:best=spread,block,deleted
    _,block,deleted=best;decoys=sorted(block-S)[:2]
    h=[x for x in p if x not in deleted];ext=sorted(deleted)+decoys
    yieldfile=D/f'control{row}.in';yieldfile.write_text(' '.join(map(str,h+ext))+'\n')
    import subprocess
    out=subprocess.check_output(['/tmp/q9_fivehost_blocks_20261121','0','191','200000',str(len(ext))],input=yieldfile.read_bytes()).decode()
    w=list(map(int,out.split(' vertices')[1].split()));assert set(w)<=set(h+ext) and len(w)==192
    print('ROW',row,'small_host',len(h),'outside_pool',len(ext),'used_outside',len(set(w)-set(h)),'vertices',*w,flush=True)

