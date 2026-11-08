"""Densely rename the verified core variables and measure optimal last-use storage."""
from pathlib import Path
import gzip,json,hashlib
H=Path(__file__).resolve().parents[1]
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
meta=json.loads((H/'data/012034-floor15-core.json').read_text())
replay=json.loads((H/'data/012034-floor15-core-replay.json').read_text())
assert replay['status']=='PASS_FULL_ORDERED_RUP_REPLAY'
source_cnf=H/'cache/012034-floor15-core.cnf';source_proof=H/'cache/012034-floor15-core.lrat'
assert sha(source_cnf)==meta['cnf_sha256'] and sha(source_proof)==meta['raw_sha256']
used=set();last={};n=meta['clauses'];derived=0
with source_cnf.open() as f:
 f.readline()
 for line in f:used.update(abs(x) for x in map(int,line.split()) if x)
with source_proof.open() as f:
 for line in f:
  xs=list(map(int,line.split()));z=xs.index(0,1);cid=xs[0]
  used.update(abs(x) for x in xs[1:z]);derived+=1
  for hint in xs[z+1:-1]:last[hint]=cid
rename={old:new for new,old in enumerate(sorted(used),1)}
def lit(x):return rename[x] if x>0 else -rename[-x]
label='012034-floor15-dense';cnf=H/'cache'/(label+'.cnf');proof=H/'cache'/(label+'.lrat')
with source_cnf.open() as src,cnf.open('w',encoding='ascii',newline='\n') as dst:
 src.readline();dst.write(f'p cnf {len(used)} {n}\n')
 for line in src:dst.write(' '.join(map(str,[*[lit(x) for x in list(map(int,line.split()))[:-1]],0]))+'\n')
expiry={}
for cid,end in last.items():expiry.setdefault(end,0);expiry[end]+=1
live=n;peak=live
with source_proof.open() as src,proof.open('w',encoding='ascii',newline='\n') as dst:
 for line in src:
  xs=list(map(int,line.split()));z=xs.index(0,1);cid=xs[0]
  dst.write(' '.join(map(str,[cid,*[lit(x) for x in xs[1:z]],0,*xs[z+1:]]))+'\n')
  # RUP reads the premises before freeing those whose last use is this step.
  # One extra slot stores the new clause. Count it before freeing old clauses.
  live+=1;peak=max(peak,live);live-=expiry.get(cid,0)
assert live==1 and peak>=n
import shutil
for suf,p in [('cnf',cnf),('lrat',proof)]:
 with p.open('rb') as src,gzip.open(H/'certificates'/(label+'.'+suf+'.gz'),'wb') as dst:shutil.copyfileobj(src,dst)
with gzip.open(H/'certificates'/(label+'.variables.json.gz'),'wt') as dst:json.dump({'dense_to_original':sorted(used)},dst)
record={'status':'UNSAT_NATIVE_REPLAY_PENDING','variables':len(used),'clauses':n,'derived_clauses':derived,
 'cnf_sha256':sha(cnf),'raw_sha256':sha(proof),'raw_bytes':proof.stat().st_size,
 'source_core_cnf_sha256':meta['cnf_sha256'],'source_core_lrat_sha256':meta['raw_sha256'],
 'producer_sha256':sha(__file__),'peak_live_with_last_use_deletions':peak,'stored_at_finish':live,
 'fits_existing_8192_variable_offset':len(used)<8192,'fits_14_bit_slots_with_this_schedule':peak<16384,
 'note':'No Lean replay has been run. Last-use deletions are measured, not emitted into this proof.'}
record['artifacts']={p.name:sha(p) for p in (H/'certificates').glob(label+'.*')}
(H/'data'/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print('DENSE',len(used),'variables; last-use peak',peak,'clauses; core proof preserved.',flush=True)
