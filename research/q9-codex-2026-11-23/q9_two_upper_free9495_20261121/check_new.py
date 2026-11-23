import gzip,shutil,subprocess,json
from pathlib import Path
from banks import D
exe=Path('/Users/yichenzhan/Documents/Codex/2026-11-02/github-app-connector-76869538009648d5b282a4bb21c3d157-x20-2/_deps/drat-trim/drat-trim')
for cutfile in sorted((D/'reroutes').glob('*.cuts.json')):
    assert json.loads(cutfile.read_text())==[]
    tag=cutfile.name.partition('.cuts.json')[0];cnf=cutfile.parent/(tag+'.cnf');drat=cutfile.parent/(tag+'.drat');p=subprocess.run([str(exe),str(cnf),str(drat)],capture_output=True);assert b's VERIFIED' in p.stdout
    for f in (cnf,drat):
        with f.open('rb') as rd,gzip.open(str(f)+'.gz','wb',compresslevel=2) as out:shutil.copyfileobj(rd,out)
    print(tag,'verified',flush=True)
