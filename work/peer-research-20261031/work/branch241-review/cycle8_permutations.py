"""Complete induced 8-cycle enumeration through a fixed oriented 3-vertex window.
An 8-cycle has <=4 coordinate directions, since every used direction occurs
an even positive number of times. An induced 8-cycle cannot use <=3 directions:
it would fill a Q3 and have degree-three chords. Thus it uses 4 directions twice.
"""
import itertools,json,argparse
from pathlib import Path

def enumerate_cycles(window,n=9):
 w=list(window)
 if len(w)!=3 or len(set(w))!=3 or any(not 0<=v<1<<n for v in w):raise ValueError('three distinct cube vertices required')
 flips=[w[i]^w[i+1] for i in range(2)]
 if any(x.bit_count()!=1 for x in flips) or flips[0]==flips[1]:raise ValueError('window must be induced 2-edge path')
 first=[x.bit_length()-1 for x in flips];found={};candidates=0
 for a,b in itertools.combinations([d for d in range(n) if d not in first],2):
  for tail in sorted(set(itertools.permutations([first[0],first[1],a,a,b,b]))):
   candidates+=1;vs=w[:]
   for d in tail:vs.append(vs[-1]^(1<<d))
   assert len(vs)==9 and vs[-1]==w[0]
   ring=vs[:-1]
   if len(set(ring))!=8:continue
   if any(((ring[i]^ring[j]).bit_count()==1)!=((j-i)==1 or (i==0 and j==7)) for i in range(8) for j in range(i+1,8)):continue
   key=tuple(sorted(ring));found[key]={'vertices':list(key),'ordered_vertices':ring,'directions':first+list(tail)}
 return {'window':w,'dimension':n,'candidate_direction_tails':candidates,'cycle_count':len(found),'cycles':[found[key] for key in sorted(found)],'completeness':'Every induced 8-cycle uses exactly four distinct coordinates, each twice; the first two fixed flips leave this exact multiset enumeration.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--window',type=int,nargs=3,default=[0,1,3]);ap.add_argument('--out',type=Path,default=Path(__file__).parent/'cycle8_manifest.json');args=ap.parse_args();data=enumerate_cycles(args.window);args.out.write_text(json.dumps(data,indent=2));print(json.dumps({k:v for k,v in data.items() if k!='cycles'},indent=2))
if __name__=='__main__':main()
