from pathlib import Path
from collections import deque
import json,gzip,subprocess,shutil,tempfile,argparse
from banks import D,path
W=(D/'donors.words').read_text().split()
exe=Path('/Users/yichenzhan/Documents/Codex/2026-11-02/github-app-connector-76869538009648d5b282a4bb21c3d157-x20-2/_deps/drat-trim/drat-trim')
options=argparse.ArgumentParser();options.add_argument('--pattern',default='sat_191_*_hint.cuts.json');args=options.parse_args()
for meta in sorted(D.glob(args.pattern)):
    tag=meta.name.partition('.cuts.json')[0];i=int(tag.split('_')[2]);q=path(W[i]);r={q[0],q[-1]};verts=sorted(set(range(256))-set(q[1:-1]));cuts=json.loads(meta.read_text())
    for clause in cuts:
        sel=set(q)|{256+t for t in r}|{256+verts[-x-1] for x in clause};assert all(x<0 for x in clause)
        nb={v:{v^1<<j for j in range(9) if v^1<<j in sel} for v in sel};todo=deque(v for v in sel if len(nb[v])<2)
        while todo:
            v=todo.popleft()
            if v not in sel:continue
            sel.remove(v)
            for u in nb[v]:
                nb[u].discard(v)
                if len(nb[u])<2:todo.append(u)
        assert sel,'false cut without a cycle'
    cnf=D/(tag+'.cnf');drat=D/(tag+'.drat')
    with tempfile.TemporaryDirectory() as temp:
        files=[]
        for file in (cnf,drat):
            archive=Path(str(file)+'.gz')
            if file.exists():files.append(file)
            else:
                local=Path(temp)/file.name
                with gzip.open(archive,'rb') as src, local.open('wb') as out:shutil.copyfileobj(src,out)
                files.append(local)
        res=subprocess.run([str(exe),*map(str,files)],capture_output=True);assert b's VERIFIED' in res.stdout
        for f,original in zip(files,(cnf,drat)):
            archive=Path(str(original)+'.gz')
            if not archive.exists():
                with f.open('rb') as inp,gzip.open(archive,'wb',compresslevel=2) as out:shutil.copyfileobj(inp,out)
    print(json.dumps(dict(donor=i,checked_cuts=len(cuts),drat_verified=True)),flush=True)
