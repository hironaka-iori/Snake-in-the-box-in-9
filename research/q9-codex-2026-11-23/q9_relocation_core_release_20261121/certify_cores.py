from repair import *
import subprocess,hashlib
checker='/Users/yichenzhan/Documents/Codex/2026-11-02/github-app-connector-76869538009648d5b282a4bb21c3d157-x20-2/_deps/drat-trim/drat-trim'
for row in map(json.loads,(B/'grown.jsonl').read_text().splitlines()):
    r=rows[row['rank']];F,x,t,_=model(r,row['mandatory'],193,r['majority'])
    with Solver(name='cadical195',bootstrap_with=F,with_proof=True) as s:
        s.conf_budget(600000);ans=s.solve_limited();res=dict(rank=row['rank'],remaining=len(row['mandatory']),removed=len(row['freed']),conflicts=s.accum_stats()['conflicts'])
        if ans is False:
            tag=f'core{r["rank"]}';cf=B/(tag+'.cnf');pf=B/(tag+'.drat');F.to_file(str(cf));pf.write_text('\n'.join(s.get_proof())+'\n')
            result=subprocess.run([checker,str(cf),str(pf)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            assert result.returncode==0 and b's VERIFIED' in result.stdout
            res.update(result='DRAT_VERIFIED',cnf_sha256=hashlib.sha256(cf.read_bytes()).hexdigest(),drat_sha256=hashlib.sha256(pf.read_bytes()).hexdigest())
        else:res['result']='UNKNOWN' if ans is None else 'SAT_RELAXATION'
        print(json.dumps(res),flush=True)
