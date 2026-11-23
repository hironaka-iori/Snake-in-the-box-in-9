from pathlib import Path
import subprocess,gzip,shutil,json
D=Path(__file__).resolve().parent;exe=Path('/Users/yichenzhan/Documents/Codex/2026-11-02/github-app-connector-76869538009648d5b282a4bb21c3d157-x20-2/_deps/drat-trim/drat-trim')
for proof in sorted(D.glob('case*.drat')):
    cnf=proof.with_suffix('.cnf');r=subprocess.run([str(exe),str(cnf),str(proof)],capture_output=True);assert b's VERIFIED' in r.stdout
    for f in (proof,cnf):
        with f.open('rb') as src,gzip.open(str(f)+'.gz','wb',compresslevel=2) as dest:shutil.copyfileobj(src,dest)
    print(json.dumps(dict(case=proof.stem,verified=True)),flush=True)
