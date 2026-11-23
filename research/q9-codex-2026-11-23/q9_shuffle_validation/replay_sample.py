import json,subprocess,gzip,shutil,tempfile
from pathlib import Path
import anywhere
from pysat.solvers import Cadical195
from pysat.formula import CNF
D=Path(__file__).resolve().parent;exe='/Users/yichenzhan/Documents/Codex/2026-11-02/github-app-connector-76869538009648d5b282a4bb21c3d157-x20-2/_deps/drat-trim/drat-trim'
class Trace(Cadical195):
    def __init__(self,bootstrap_with):
        self.initial=bootstrap_with;super().__init__(bootstrap_with=bootstrap_with,with_proof=True)
    def __exit__(self,*args):
        CNF(from_clauses=self.initial).to_file(str(cnf));proof.write_text('\n'.join(self.get_proof())+'\n');super().__exit__(*args)
anywhere.Cadical195=Trace
for n in (195,196):
    r=json.loads((D/f'any{n}.jsonl').read_text().splitlines()[0])
    with tempfile.TemporaryDirectory(dir=D) as td:
        cnf=Path(td)/'s.cnf';proof=Path(td)/'s.drat';st,c,p,u=anywhere.unrestricted(list(map(int,r['w'])),60000);assert st=='UNSAT'
        result=subprocess.run([exe,str(cnf),str(proof)],capture_output=True);assert b's VERIFIED' in result.stdout
        for v in (cnf,proof):
            with v.open('rb') as src,gzip.open(D/f'physical{n}{v.suffix}.gz','wb') as dst:shutil.copyfileobj(src,dst)
    print(json.dumps(dict(n=n,row=0,src=r['src'],i=r['i'],verified=True)))
