"""Certify a genuinely feasible plain window with a share cap, using fresh proof runs."""
import gzip,hashlib,json,time
from pathlib import Path
from tagged_share import HERE,TaggedShare,Cadical153,cycles_of

def main():
    row=1;record=json.loads((HERE/'data/cache-obstruction.json').read_text())['records'][row]
    dirs,bounds=record['five_window_key'];enc=TaggedShare(dirs,bounds,107);prefix=HERE/'certificates/share1'
    screen=json.loads((HERE/'data/plain-screen.json').read_text())['rows'][row]
    assert screen['status']=='SAT'
    for cc in screen['cycle_cuts']:enc.add([-enc.var[v] for v in cc],('old',('cut',)))
    allcuts=list(screen['cycle_cuts']);t=time.monotonic();deadline=t+90;status='UNKNOWN';witness=None;proof=[]
    while time.monotonic()<deadline:
        with Cadical153(bootstrap_with=enc.clauses,with_proof=True) as s:
            while time.monotonic()<deadline:
                s.conf_budget(10000);ok=s.solve_limited()
                if ok is not None:break
            else:break
            if not ok:status='UNSAT';proof=s.get_proof();break
            model=s.get_model();witness=[v for v in enc.ball if model[enc.var[v]-1]>0];cycles=cycles_of(witness)
            if not cycles:status='SAT';break
            for cc in cycles:enc.add([-enc.var[v] for v in cc],('old',('cut',)));allcuts.append(cc)
        print('restart with',len(allcuts),'cycle cuts',flush=True)
    with prefix.with_suffix('.cnf').open('w') as f:
        f.write(f'p cnf {enc.nv} {len(enc.clauses)}\n')
        for cl in enc.clauses:f.write(' '.join(map(str,cl))+' 0\n')
    if proof:prefix.with_suffix('.drat').write_text('\n'.join(proof)+'\n')
    with gzip.open(prefix.with_suffix('.meanings.json.gz'),'wt') as f:json.dump(dict(meaning=enc.meaning,smeaning=enc.smeaning,ctrs=enc.ctrs,tots=enc.tots,tags=enc.tags),f)
    meta=dict(row=row,dirs=dirs,bounds=bounds,window=enc.window,cap=107,M=12,status=status,variables=enc.nv,clauses=len(enc.clauses),cycle_cuts=allcuts,seconds=round(time.monotonic()-t,3),selected=witness if status=='SAT' else None,plain_window_status='SAT',script_sha256_lf=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),encoder_sha256_lf=hashlib.sha256((HERE/'scripts/tagged_share.py').read_bytes().replace(b'\r\n',b'\n')).hexdigest())
    prefix.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps({k:v for k,v in meta.items() if k not in ('cycle_cuts','selected')}),flush=True)
if __name__=='__main__':main()
