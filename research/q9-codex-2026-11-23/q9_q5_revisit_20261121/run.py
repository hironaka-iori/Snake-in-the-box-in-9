from prepare import *
import sys
sys.path.insert(0,str(R))
from search_q9_anchored_sets import search
from retry_q9_six_cube_sites_cadical import search as second
W=(R/'q9_gap_generations/prior191.words').read_text().split();P=list(map(path,W));S=list(map(set,P))
def rows(f):return list(map(json.loads,(D/f).read_text().splitlines()))
def dom(r):
 A=r['a'];F=set(r['f']);src=S[r['r']]
 free={v for v in range(512) if lay(v,A) in F};fixed=src-free
 return fixed,fixed|free
def run():
 mode=sys.argv[1];budget=int(sys.argv[2]);source=rows('controls.jsonl' if mode in ('control','warm','partial') else 'cases.jsonl')
 if mode in ('control','warm','partial'):ids=list(range(len(source)))
 elif sys.argv[3]=='all':ids=list(range(len(source)))
 elif sys.argv[3].isdigit():ids=list(range(0,len(source),int(sys.argv[3])))
 else:ids=list(map(int,(D/sys.argv[3]).read_text().split()))
 for i in ids:
  r=source[i];fix,allowed=dom(r);a=r['a'];src=P[r['r']];hint=set(src)
  if mode in ('control','warm','partial'):
   alt=P[r['t']];assert S[r['t']]-allowed==set() and fix<=S[r['t']];old=norm(seq(src,a))
   required=sorted(S[r['t']]-hint)[:1];fix.update(required)
   if mode=='partial':fix.update(sorted(S[r['t']]&allowed-set(fix))[::2])
   z,p=search(fix,set(alt) if mode=='warm' else set(),191,budget,allowed=allowed,reject_fragment=lambda q: q if norm(seq(q,a))==old else None)
  elif mode=='cad':z,p=second(fix,hint,192,budget,allowed=allowed)
  else:z,p=search(fix,hint,192,budget,allowed=allowed,at_least=True)
  print(json.dumps([i,z,p],separators=(',',':')),flush=True)
  if p and mode not in ('control','warm','partial'):return
if __name__=='__main__':run()
