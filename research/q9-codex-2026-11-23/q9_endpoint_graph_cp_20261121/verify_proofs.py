import hashlib,json,os,subprocess,sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
B=Path(__file__).resolve().parent
checker=Path(os.getenv('DRAT_TRIM','/Users/yichenzhan/Documents/Codex/2026-11-02/github-app-connector-76869538009648d5b282a4bb21c3d157-x20-2/_deps/drat-trim/drat-trim'))
store=B/'proofs_checked.jsonl'
seen={} if not store.exists() else {r['rank']:r for r in map(json.loads,store.read_text().splitlines())}
ranks=set()
for log in sys.argv[1:]:
    for l in (B/log).read_text().splitlines():
        r=json.loads(l)
        if r['result']=='CNF_UNSAT':ranks.add(r['rank'])
def check(i):
    cnf=B/f'rank{i}.cnf';proof=B/f'rank{i}.drat'
    z=subprocess.run([str(checker),str(cnf),str(proof)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    assert z.returncode==0 and b's VERIFIED' in z.stdout,(i,z.stdout[-300:])
    return dict(rank=i,result='DRAT_VERIFIED',cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest(),proof_sha256=hashlib.sha256(proof.read_bytes()).hexdigest())
with store.open('a') as f,ThreadPoolExecutor(max_workers=3) as pool:
    for r in pool.map(check,sorted(ranks-seen.keys())):f.write(json.dumps(r)+'\n');f.flush()
print('independent DRAT checks:',len(seen.keys()|ranks))
