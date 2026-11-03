"""Check two saved cycles and a uniform-credit comparison, without graph search."""
from pathlib import Path
from fractions import Fraction
import datetime,gc,hashlib,json,zipfile
import numpy as np

H=Path(__file__).resolve().parents[1];R=H.parents[1];pins={}
def sha(p):
 p=Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 value=h.hexdigest();pins[p.relative_to(R).as_posix()]=value;return value
def read(p):sha(p);return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def canon(w):
 names={};return tuple(names.setdefault(x,len(names)) for x in w)
def shape(w):return min(canon(w),canon(w[::-1]))
def main():
 sha(Path(__file__))
 source=R/'milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json'
 result=read(source)
 review=read(R/'milestones/131-odd-pair-six-count/data/graph-review.json')
 assert result['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
 assert review['status']=='PASS_STATIC_AND_INDEPENDENT_SAVED_CYCLE_REVIEW'
 assert pins[source.relative_to(R).as_posix()]==review['source_files_sha256'][source.relative_to(R).as_posix()]
 assert review['all_source_array_hashes_verified']
 meta=read(R/'milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
 graph=R/'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
 assert sha(graph)==result['source_files_sha256'][graph.relative_to(R).as_posix()]
 with zipfile.ZipFile(graph) as z:assert z.getinfo('weight.npy').file_size<150_000_000
 selected={e['edge'] for p in result['profiles'] for e in p['cycle']}
 with np.load(graph) as z:
  weight=z['weight'];assert weight.nbytes<150_000_000
  assert hashlib.sha256(memoryview(weight)).hexdigest()==meta['arrays_sha256']['weight']
  original={k:int(weight[k]) for k in selected};array_bytes=weight.nbytes
  del weight;gc.collect()
 floors=read(R/'milestones/73-countfree-share-catalogue/data/proved-model.json')
 floors={tuple(x['shape']):x['share'] for x in floors['countfree_floors']}
 ds=read(R/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
 cycles=[]
 for p in result['profiles']:
  rows=[];events=[];prefix=[]
  for e in p['cycle']:
   w=e['directions'];c=e['counts'];k=e['edge']
   assert w==ds[e['direction']]
   assert c==[e['count_code']//6**j%6+1 for j in range(5,-1,-1)]
   old_bonus=0
   for rule in result['rules']:
    target=shape(rule['directions']);word=w[3:9];five=c[1:6]
    if shape(word)!=target:continue
    if canon(word)!=target:five=five[::-1]
    if all(lo<=x and (21 if x==6 else x)<=hi for x,(lo,hi) in zip(five,rule['bounds'])):
     old_bonus=max(old_bonus,24*max(0,rule['lower']-sum(five[j] for j in rule['positions'])))
   pair_bonus=0
   for s in [0,1]:
    if shape(w[s+2:s+8])!=(0,1,2,0,3,2):continue
    a,b=c[s+1],c[s+3]
    assert not (a<6 and b<6 and a+b<9)
    if s==1:pair_bonus=24*max(0,9-a-b)
    if a<6 and b<6 and a+b==9:
     (events if s==1 else prefix).append(dict(edge=k,pair=[a,b],placement=s))
   match=shape(w[2:])==shape([0,1,2,3,1,0,4])
   six_bonus=24*max(0,25-sum(c)) if match and c[0]<6 else 0
   shared=max(old_bonus,pair_bonus,six_bonus)
   assert (old_bonus,pair_bonus,six_bonus,shared)==(e['old_bonus24'],e['pair_bonus24'],e['six_bonus24'],e['shared_bonus'])
   suffix=shape(w[-6:]);floor=floors.get(suffix,0)
   base=max(original[k],120*c[-1]+floor)
   rows.append(dict(edge=k,u=e['u'],v=e['v'],original_weight=original[k],last_count=c[-1],
    suffix_shape=list(suffix),countfree_floor=floor,base_weight=base,shared_bonus=shared,
    first_profile_weight=base+shared))
  assert all(e['v']==rows[(j+1)%len(rows)]['u'] for j,e in enumerate(rows))
  total=sum(e['first_profile_weight'] for e in rows)
  cycles.append(dict(source_profile=p['profile'],rows=rows,weights=[e['first_profile_weight'] for e in rows],
   total=total,mean=str(Fraction(total,len(rows))),suffix_pair9_events=events,prefix_pair9_matches=prefix))
 four,seven=cycles
 assert len(four['rows'])==4 and four['total']==1952 and four['mean']=='488'
 assert len(four['suffix_pair9_events'])==2 and len(four['prefix_pair9_matches'])==2
 assert seven['weights']==[732,376,366,376,616,251,736]
 assert seven['total']==3453 and seven['mean']=='3453/7'
 assert not seven['suffix_pair9_events'] and not seven['prefix_pair9_matches']
 # Exact rational coefficient check of the nonnegative decomposition.
 assert 1098960-235*4200==111960 and 235-8==227
 assert Fraction(1952)+223*Fraction(3453,7)+Fraction(37,7)==111960
 assert -4-223==-227
 assert Fraction(110008)-223*Fraction(3453,7)==Fraction(37,7)
 denominator_max=4200+Fraction(3453,7)
 gap=Fraction(37,7)/denominator_max
 assert denominator_max==Fraction(32853,7) and gap==Fraction(37,32853)
 # The lower comparison value is attained in this arithmetic domain.
 mu=Fraction(3453,7);credit=Fraction(74,7)
 assert mu==488+credit/2
 arithmetic_minimum=Fraction(1098960+8*mu+2*credit,4200+mu)
 assert arithmetic_minimum==235+gap
 out=dict(status='PASS_TWO_CYCLES_AND_UNIFORM_CREDIT_LIMITATION',cycles=cycles,
  original_weight_array_bytes=array_bytes,original_weight_array_loaded_once=True,
  other_source_rows='Reused the independently source-checked milestone131 rows; their result hash was verified.',
  cap_statements=['mu <= 488 + C/2','mu <= 3453/7'],
  assumptions=['C >= 0','R >= 0','mu >= 0','The same fixed retained graph and base weights are used.',
   'Only a uniform credit C on each exact pair-sum-nine suffix event is added.',
   'The charge comparison allows two such events, hence adds 2C to its numerator.'],
  nonnegative_decomposition='Numerator minus235 times denominator = (2C -4mu +1952) +223(3453/7 -mu) +R +37/7.',
  numerator_difference_lower='37/7',comparison_lower=str(arithmetic_minimum),
  comparison_gap_above235=str(gap),arithmetic_equality_parameters=dict(mu=str(mu),C=str(credit),R='0'),
  limitations=['This is a fixed-model uniform-credit limitation, not a global impossibility result.',
   'It does not refute any proposed endpoint property.',
   'It does not cover nonuniform credits, extra state restrictions, edge deletions or a different charge comparison.',
   'No Lean, solver, or full-graph calculation was run.'],
  completed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_files_sha256=pins)
 destination=H/'data/credit-limitation.json';assert not destination.exists()
 destination.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
 print(json.dumps({k:v for k,v in out.items() if k not in ['cycles','source_files_sha256']},indent=2))
 print('First-profile cycle weights',four['weights'],seven['weights'])
if __name__=='__main__':main()
