"""Isolated KEEP=96 paths and atomic, content-addressed records."""
import hashlib,json,os,sys,time,gzip
from pathlib import Path
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=ROOT/'outputs/lean96'
BANK=HERE/'bank'
CACHE=OUT/'cache'
for p in (OUT,BANK,CACHE,OUT/'logs',OUT/'artifacts',OUT/'cores'):p.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(HERE/'.packages'))
sys.path.insert(0,str(ROOT/'work'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def read(p,default=None):
    return json.loads(Path(p).read_text(encoding='utf-8')) if Path(p).exists() else default
def save(p,value):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
    tmp=p.with_name(p.name+'.'+str(os.getpid())+'.'+str(time.time_ns())+'.tmp')
    tmp.write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    for attempt in range(10):
        try:
            os.replace(tmp,p)
            break
        except PermissionError:
            if attempt==9:raise
            time.sleep(0.05*(attempt+1))
def now():return datetime.now(timezone.utc).isoformat()
def formula(i):return json.loads(gzip.decompress((ROOT/f'outputs/keep96/formulas/entry{i:03d}.json.gz').read_bytes()))
