from pathlib import Path
import os,json,subprocess,gzip,shutil,sys
from banks import D,path
from sat import R,W,search
os.environ['Q9_NO_PINS']='1';os.environ['Q9_EXPORT_PROOF']='1'
exe=Path('/Users/yichenzhan/Documents/Codex/2026-11-02/github-app-connector-76869538009648d5b282a4bb21c3d157-x20-2/_deps/drat-trim/drat-trim')
for i in map(int,sys.argv[1].split(',')):
    _,_,_,_,a,b=R[str(i)];arms=path(a),path(b,path(W[i])[-1])
    for c in (0,1):
        tag=D/f'sat_192_{i}_{c}_hint';search(i,c,192,int(sys.argv[2]),arms);cnf=tag.with_suffix('.cnf');drat=tag.with_suffix('.drat')
        if not cnf.exists():continue
        p=subprocess.run([str(exe),str(cnf),str(drat)],capture_output=True)
        ok=b's VERIFIED' in p.stdout;assert ok
        for f in (cnf,drat):
            with f.open('rb') as inp,gzip.open(str(f)+'.gz','wb',compresslevel=2) as out:shutil.copyfileobj(inp,out)
            f.unlink()
        print(json.dumps(dict(id=i,c=c,drat_verified=ok,cycles=json.loads(tag.with_suffix('.cuts.json').read_text()))),flush=True)
