from complete import *
import os,hashlib,tempfile,subprocess
from zlib import compress,decompress
from collections import Counter
from contextlib import nullcontext
CA=Path.home()/'.elan/toolchains/leanprover--lean4---v4.19.0/bin/cadical'
def check(cla,proof):
 db={i:c for i,c in enumerate(cla,1)};stats=Counter();isfalse=False
 for line in proof.splitlines():
  bits=line.split()
  if bits[1]==b'd':
   for rid in bits[2:-1]:db.pop(int(rid),None)
   continue
  i,*vals=map(int,bits);sep=vals.index(0);lits=vals[:sep];hints=vals[sep+1:-1]
  assert i not in db and vals[-1]==0 and hints and min(hints)>0
  values={-a for a in lits};conflict=False
  for h in hints:
   c=db[h];assert not any(a in values for a in c);open_=[a for a in c if -a not in values]
   if len(open_)==0:conflict=True;break
   assert len(open_)==1;values.add(open_[0])
  assert conflict
  isfalse|=not lits;db[i]=lits;stats['steps']+=1
 assert isfalse;return stats['steps']
def main():
 archive=D/'proofs';checkonly='--check' in sys.argv
 if not checkonly:archive.mkdir(exist_ok=True)
 memo={};seen=0;pilot='pilot' in sys.argv
 with (nullcontext(D) if checkonly else tempfile.TemporaryDirectory(dir=D)) as tmp:
  cnf=Path(tmp)/'generated.cnf';proof=Path(tmp)/'generated.lrat'
  for source in ('tail','head','integral'):
   for i,line in enumerate((D/(source+'.work')).read_text().splitlines()):
    row,d,t,a,j,L,R,rem,np,*c=map(int,line.split());N,cla=complete(c,L,R,rem,cnf_only=True)
    dim=(f'p cnf {N} {len(cla)}\n'+''.join(' '.join(map(str,cl))+' 0\n' for cl in cla)).encode();dig=hashlib.sha256(dim).hexdigest();path=archive/(dig+'.zz')
    if dig not in memo:
     if not path.exists():
      assert not checkonly, f'missing proof {dig}'
      cnf.write_bytes(dim);res=subprocess.run([str(CA),'--plain','--lrat','--no-binary','-q',str(cnf),str(proof)],capture_output=True)
      assert res.returncode==20,(res.returncode,res.stdout,res.stderr)
      blob=proof.read_bytes();path.write_bytes(compress(blob,6))
     blob=decompress(path.read_bytes());memo[dig]=[check(cla,blob),len(blob)]
    print(json.dumps([source,i,dig,*memo[dig]],separators=(',',':')),flush=True)
    seen+=1
    if pilot and seen>=3:return
if __name__=='__main__':main()
