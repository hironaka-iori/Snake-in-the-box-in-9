"""Produce and trim a genuine empty-square share refutation."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
def run(cmd,log,expected):
 with log.open('w',encoding='utf-8') as f:r=subprocess.run(list(map(str,cmd)),stdout=f,stderr=subprocess.STDOUT,timeout=240)
 assert r.returncode==expected,(cmd,r.returncode)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--row',type=int,default=3);ap.add_argument('--cap',type=int,default=47);args=ap.parse_args()
 row=json.loads((HERE/'pass5/data/critical-family.json').read_text())['windows'][args.row]
 bounds=[[6,21] if c==6 else [c,c] for c in row['counts']];name=f'share{args.row}_{args.cap}';prefix=HERE/'certificates'/name;prefix.parent.mkdir(exist_ok=True)
 t=time.monotonic();enc=TaggedShare(row['directions'],bounds,args.cap)
 print('Encoded',enc.nv,'variables',len(enc.clauses),'clauses',round(time.monotonic()-t,2),'seconds',flush=True)
 full=prefix.with_suffix('.full.cnf');full.write_text(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses))
 with gzip.open(prefix.with_suffix('.meanings.json.gz'),'wt') as f:json.dump(dict(meaning=enc.meaning,smeaning=enc.smeaning,ctrs=enc.ctrs,tots=enc.tots,tags=enc.tags),f)
 run([BIN/'cadical.exe','-q','--no-binary',full,prefix.with_suffix('.drat')],HERE/f'logs/{name}-cadical.txt',20)
 print('Native UNSAT',round(time.monotonic()-t,2),flush=True)
 run([ROOT/'work/share-wheels/drat-trim.exe',full,prefix.with_suffix('.drat'),'-c',prefix.with_suffix('.core.cnf')],HERE/f'logs/{name}-drat-check.txt',0)
 assert 's VERIFIED' in (HERE/f'logs/{name}-drat-check.txt').read_text()
 read=lambda p:[list(map(int,l.split()))[:-1] for l in p.read_text().splitlines() if l and not l.startswith(('c','p'))]
 core=read(prefix.with_suffix('.core.cnf'));lookup={tuple(sorted(c)):i for i,c in enumerate(enc.clauses)};ids=[lookup[tuple(sorted(c))] for c in core]
 kinds={}
 for i in ids:k=enc.tags[i][0];kinds[k]=kinds.get(k,0)+1
 assert any(k!='old' for k in kinds),'A share-free core gives no genuine share result.'
 meta=dict(name=name,row=args.row,directions=row['directions'],counts=row['counts'],bounds=bounds,cap=args.cap,window=enc.window,variables=enc.nv,clauses=len(enc.clauses),core_clauses=len(core),source_original_clause_ids=[i+1 for i in ids],families=kinds,seconds=time.monotonic()-t,scope='Native refutation checked with drat-trim; Lean replay and geometric interpretation still required.')
 (HERE/f'data/{name}.json').write_text(json.dumps(meta,indent=2)+'\n');print({k:v for k,v in meta.items() if k!='source_original_clause_ids'},flush=True)
if __name__=='__main__':main()
