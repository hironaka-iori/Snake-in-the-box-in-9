from pathlib import Path
import json,subprocess,tempfile,gzip,shutil
import fixedproof as m
D=Path(__file__).resolve().parent;exe='/Users/yichenzhan/Documents/Codex/2026-11-02/github-app-connector-76869538009648d5b282a4bb21c3d157-x20-2/_deps/drat-trim/drat-trim'
h={v-256 for v in json.loads((D/'cases.json').read_text())[0]['hint'] if v>=256}
for i,(q,s) in enumerate(m.load(D/'fullalt_0.dat')+m.load(D/'fullalt_1.dat')):
    for c in (0,1):
        m.run(q,s,192,c,225000,i,'fixedproof',h);t=D/f'fixed{i}c{c}';f=t.with_suffix('.cnf');p=t.with_suffix('.drat')
        ans=subprocess.run([exe,str(f),str(p)],capture_output=True);assert b's VERIFIED' in ans.stdout
        for src in (f,p):
            with src.open('rb') as a,gzip.open(str(src)+'.gz','wb',compresslevel=2) as b:shutil.copyfileobj(a,b)
            src.unlink()
        print(json.dumps(dict(i=i,c=c,drat=True)),flush=True)
