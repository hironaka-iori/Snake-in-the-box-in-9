"""Independent bounded source and saved-cycle review; never runs a graph search."""
from pathlib import Path
from fractions import Fraction
import ast, datetime, gc, gzip, hashlib, itertools, json, subprocess, time, traceback, zipfile
import numpy as np

H=Path(__file__).resolve().parents[1]; R=H.parents[1]
F=H/'data/odd-pair9-six25'; P=R/'milestones/130-fourth-count-large'
PINS={}
def sha(p):
 p=Path(p); h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''): h.update(b)
 value=h.hexdigest(); PINS[p.relative_to(R).as_posix()]=value; return value
def read(p):
 sha(p); return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def canon(w):
 names={}; return tuple(names.setdefault(int(x),len(names)) for x in w)
def shape(w): return min(canon(w),canon(w[::-1]))
def main():
 start=time.monotonic(); sha(Path(__file__))
 original=R/'milestones/124-six-count-cycle-pressure/scripts/evaluate_six_shapes.py'
 gen=H/'scripts/prepare_graph.py'; evaluator=H/'scripts/evaluate_graph.py'
 src=evaluator.read_text(); ast.parse(src)
 literals={}
 for n in ast.parse(gen.read_text()).body:
  if isinstance(n,ast.Assign) and isinstance(n.value,ast.Constant) and isinstance(n.value.value,str):
   for t in n.targets:
    if isinstance(t,ast.Name): literals[t.id]=n.value.value
 prefix=original.read_text(encoding='utf-8-sig').split('old_bonus24=bonus.copy()')[0]
 prefix=prefix[prefix.index('from pathlib import Path'):].replace("label = args.label or 'graph-26-25-25'","label = args.label or 'odd-pair9-six25'")
 rebuilt=literals['WRAPPER']+'\nDERIVED_SOURCE_SHA256 = '+repr(sha(original))+'\n'+prefix+literals['SUFFIX']
 assert rebuilt==src
 prep=read(H/'data/preparation-note.json')
 assert sha(gen)==prep['prepare_sha256'] and sha(evaluator)==prep['evaluate_sha256']
 assert sha(original)==prep['source_sha256']
 assert sha(F/'evaluate_graph.exact.py')==sha(evaluator)
 required=['for s in range(2):','for reverse in [False, True]:',
  'rejected[lo:hi] = (a < 6) & (b < 6) & (a+b < 9)',
  'six_guard = six_match & (digits[:,0] < 6)',
  'six_reject = six_match & np.all(digits < 6,axis=1) & (six_sum < 25)',
  'shared = np.maximum(np.maximum(old_bonus24,pair_bonus),six_bonus)',
  'assert 1503*step_bound < 2**62','np.minimum.at(nxt,v,dist[u]+d*W-p)',
  'assert np.all(slack >= 0)','assert np.all(slack[ci] == 0)',
  'assert saved_mean == Fraction(3011,6)',
  "assert sha(full_baselines[name][keep].tobytes())==previous121_profiles[name]['weight_sha256']",
  'assert np.array_equal(removed,np.array(previous121_removed))']
 assert all(s in src for s in required)
 parity=read(P/'data/odd-pair-verification.json')
 assert parity['status']=='PASS_ACTUAL_PARITY_PAIR_NINE' and parity['length235_specialization_checked']
 for rel,digest in parity['pins'].items(): assert sha(P/rel)==digest
 theorem=(P/'lean/OddPair130.lean').read_text()
 assert '(hshape : canon (dsOf p r 6) = [0,1,2,0,3,2]) (hodd : m % 2 = 1)' in theorem
 assert '9 ≤ coreAlpha p (r+2) + coreAlpha p (r+4)' in theorem
 pair_cases=0
 for a,b in itertools.product(range(1,22),repeat=2):
  x,y=min(a,6),min(b,6); reject=x<6 and y<6 and x+y<9
  assert not reject or a+b<9
  if a+b>=9: assert max(0,9-x-y)<=(a-x)+(b-y)
  pair_cases+=1
 six_cases=0
 for c in itertools.product(range(1,7),repeat=6):
  guard=c[0]<6; reject=all(x<6 for x in c) and sum(c)<25
  assert not reject or guard
  if guard and sum(21 if x==6 else x for x in c)>=25:
   assert max(0,25-sum(c))<=sum(21-x if x==6 else 0 for x in c[1:])
  six_cases+=1
 out=dict(status='PASS_STATIC_REVIEW_RESULT_PENDING',static_review=True,
  inherited124_prefix_exact=True,preparation_and_snapshot_hashes_match=True,
  actual_pair_cases=pair_cases,clipped_six_cases=six_cases,
  parity_receipt_verified=True,all_edge_algorithm_reviewed=True,
  all_edge_inequalities_independently_recomputed=False,
  limitations=['No independent rerun of the full graph or its all-edge inequalities.',
   'Both graph profiles retain inherited unproved count-sum hypotheses.',
   'The conditional_floor18 profile retains additional share-floor hypotheses.',
   'The 0123104 six-count floor25 is hypothetical.',
   'Pair9 applies to odd snake length; graph-to-snake coverage and charge assembly remain pending.',
   'No new actual-snake upper bound is established.'])
 # The wait is bounded independently of the evaluator's longer timeout.
 deadline=time.monotonic()+240
 while True:
  run=json.loads((F/'run-status.json').read_text())
  if run['status']!='RUNNING': break
  if time.monotonic()>=deadline: break
  time.sleep(min(30,deadline-time.monotonic()))
 out['observed_run_status']=run['status']
 if run['status']!='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA':
  out['result_review']='No successful terminal result was available within the bounded wait.'
  out['observed_run_record']=run
  return out,start
 run=read(F/'run-status.json'); result=read(F/'results.json')
 assert run['returncode']==0 and result['status']==run['status']
 assert run['script_sha256']==result['script_sha256']==sha(evaluator)
 assert run['resources']['free_bytes']>=3*1024**3 and not run['resources']['other_fullgraph_processes']
 worker=read(F/'worker-resources.json')
 assert worker['free_bytes']>=3*1024**3 and not worker['other_fullgraph_processes']
 launch=read(H/'data/odd-pair9-six25-launch.json')
 assert launch['script_sha256']==sha(H/'scripts/run_ready.py')
 for rel,digest in result['source_files_sha256'].items(): assert sha(R/rel)==digest,rel
 ref='41797e3863e17be730f06e3a9c5df09bbc0d404d'; filename='milestones/10-window-aggregate/scripts/refine.py'
 alg=subprocess.check_output(['git','show',ref+':'+filename],cwd=R).decode().replace('\r\n','\n')
 assert hashlib.sha256(alg.encode()).hexdigest()==result['algorithm_sha256']
 sha(R/'milestones/51-exact-bucket-pressure/scripts/analyze_share.py')
 assert result['coefficients']==[24]*5 and result['odd_length_pair_floor']==9
 assert result['six_count_hypothesis']['floor']==25 and not result['six_count_hypothesis']['lean_proof_complete']
 assert result['shared_bonus_is_maximum'] and result['old_bonus_preserved']
 assert result['baseline121_weight_hashes_reproduced'] and result['baseline121_removals_reproduced']
 meta=read(R/'milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
 old=read(R/'milestones/121-replacement-window-pressure/data/pair-graph/results.json')
 old_completed=next(p for p in old['profiles'] if p['profile']=='completed')['cycle']
 chosen=set(e['edge'] for p in result['profiles'] for e in p['cycle'])|{e['edge'] for e in old_completed}
 selected=np.array(sorted(chosen),dtype=np.int64)
 graph=R/'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
 rows={int(k):{} for k in selected}; sizes=[]
 with zipfile.ZipFile(graph) as archive:
  sizes=[i.file_size for i in archive.infolist()]
  assert max(sizes)<150_000_000
 # Exactly one member at a time; retain only selected scalar rows.
 with np.load(graph) as z:
  for name in z.files:
   a=z[name]; assert a.nbytes<150_000_000
   assert hashlib.sha256(memoryview(a)).hexdigest()==meta['arrays_sha256'][name]
   if name=='direction': assert np.all(a[1:]>=a[:-1])
   for k,value in zip(selected,a[selected]): rows[int(k)][name]=int(value)
   del a; gc.collect()
 ds=read(R/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
 completed=read(R/'milestones/73-countfree-share-catalogue/data/proved-model.json')
 floors={tuple(r['shape']):r['share'] for r in completed['countfree_floors']}
 additional={(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
 def evaluate(k,profile):
  a=rows[k]; w=ds[a['direction']]; c=[a['count_code']//6**j%6+1 for j in range(5,-1,-1)]
  credit=0
  for rule in result['rules']:
   word=w[3:9]; five=c[1:6]; target=shape(rule['directions'])
   if shape(word)!=target: continue
   if canon(word)!=target: five=five[::-1]
   if all(x>=lo and (21 if x==6 else x)<=hi for x,(lo,hi) in zip(five,rule['bounds'])):
    credit=max(credit,24*max(0,rule['lower']-sum(five[j] for j in rule['positions'])))
  pair=0; rejected=False
  for s in range(2):
   if shape(w[s+2:s+8])!=(0,1,2,0,3,2): continue
   x,y=c[s+1],c[s+3]
   rejected|=x<6 and y<6 and x+y<9
   if s==1: pair=24*max(0,9-x-y)
  match=shape(w[2:])==shape([0,1,2,3,1,0,4]); guard=match and c[0]<6
  rejected|=match and all(x<6 for x in c) and sum(c)<25
  six=24*max(0,25-sum(c)) if guard else 0
  chosen_floors=floors if profile=='completed' else floors|additional
  base=max(a['weight'],120*c[-1]+chosen_floors.get(shape(w[-6:]),0))
  return dict(edge=k,u=a['U'],v=a['V'],direction=a['direction'],history=a['history'],
   count_code=a['count_code'],directions=w,counts=c,base_weight=base,old_bonus24=credit,
   pair_bonus24=pair,six_bonus24=six,shared_bonus=max(credit,pair,six),
   weight=base+max(credit,pair,six),six_shape_matches=match,six_guard=guard),rejected
 reviews=[]
 for p in result['profiles']:
  assert read(F/(p['profile']+'-profile.json'))==p
  rebuilt=[]
  for e in p['cycle']:
   row,removed=evaluate(e['edge'],p['profile']); assert not removed and row==e
   rebuilt.append(row)
  assert all(e['v']==rebuilt[(j+1)%len(rebuilt)]['u'] for j,e in enumerate(rebuilt))
  mu=Fraction(sum(e['weight'] for e in rebuilt),len(rebuilt))
  assert str(mu)==p['mean'] and (mu.numerator,mu.denominator)==(p['p'],p['d'])
  potpath=F/p['potential_file']; sha(potpath); raw=gzip.decompress(potpath.read_bytes())
  assert hashlib.sha256(raw).hexdigest()==p['potential_sha256']
  potential=np.frombuffer(raw,dtype='<i8')
  assert len(potential)==result['states']==meta['states']
  assert int(potential.min())==0 and int(potential.max())==p['range_scaled']
  slack=[p['d']*e['weight']+int(potential[e['u']])-p['p']-int(potential[e['v']]) for e in rebuilt]
  assert all(x==0 for x in slack)
  assert p['all_edge_inequalities_checked'] and p['inequalities_checked']==result['edges'] and p['minimum_slack']==0
  assert 1<=p['iterations']<=1500 and p['cycle_attaining']
  comparison=Fraction(1098960*p['d']+8*p['p']+p['range_scaled'],4200*p['d']+p['p'])
  assert str(comparison)==p['comparison_bound'] and comparison.numerator//comparison.denominator==p['comparison_integer_bound']
  reviews.append(dict(profile=p['profile'],mean=str(mu),cycle_length=len(rebuilt),cycle_weights_source_checked=True,
   cycle_potential_slacks=slack,potential_range=p['range_scaled'],comparison=str(comparison)))
  del potential,raw; gc.collect()
 saved=[evaluate(e['edge'],'completed') for e in old_completed]
 assert len(saved)==18 and all(not rejected for row,rejected in saved)
 assert all(row['v']==saved[(j+1)%18][0]['u'] for j,(row,_) in enumerate(saved))
 saved_mean=Fraction(sum(row['weight'] for row,_ in saved),18)
 assert saved_mean==Fraction(3011,6) and str(saved_mean)==result['saved18_cycle_hypothetical_mean']
 out.update(status='PASS_STATIC_AND_INDEPENDENT_SAVED_CYCLE_REVIEW',profiles=reviews,
  selected_original_edges=len(selected),npz_members_read_once=True,largest_array_bytes=max(sizes)-128,
  all_source_array_hashes_verified=True,source_direction_sorted=True,saved18_mean=str(saved_mean),
  result_source_pins_verified=len(result['source_files_sha256']),run_source_hashes_verified=True)
 sha(F/'stdout.log'); sha(F/'stderr.log')
 return out,start

def add_saved_comparison(destination):
 """Extend an existing successful review using its already checked cycle rows."""
 initial_hash=sha(destination); out=read(destination)
 assert out['status']=='PASS_STATIC_AND_INDEPENDENT_SAVED_CYCLE_REVIEW'
 assert 'baseline_comparison' not in out
 result=read(F/'results.json')
 old=read(R/'milestones/121-replacement-window-pressure/data/pair-graph/results.json')
 for rel in ['milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json',
             'milestones/121-replacement-window-pressure/data/pair-graph/results.json']:
  assert PINS[rel]==out['source_files_sha256'][rel]
 comparisons=[]; obstructions=[]
 for p in result['profiles']:
  before=next(q for q in old['profiles'] if q['profile']==p['profile'])
  comparisons.append(dict(profile=p['profile'],baseline_mean=before['mean'],new_mean=p['mean'],
   mean_increase=str(Fraction(p['mean'])-Fraction(before['mean'])),baseline_range=before['range'],new_range=p['range'],
   baseline_comparison=before['comparison_bound'],new_comparison=p['comparison_bound'],
   baseline_integer=before['comparison_integer_bound'],new_integer=p['comparison_integer_bound']))
  pairs=[]; shapes=[]
  for e in p['cycle']:
   w=e['directions'];c=e['counts']; shapes.append(list(shape(w[2:])))
   assert shape(w[2:])!=shape([0,1,2,3,1,0,4])
   assert e['pair_bonus24']==e['six_bonus24']==0
   for s in range(2):
    if shape(w[s+2:s+8])==(0,1,2,0,3,2):
     a,b=c[s+1],c[s+3]
     assert a+b>=9
     pairs.append(dict(edge=e['edge'],placement=s,pair=[a,b],sum=a+b))
  obstructions.append(dict(profile=p['profile'],canonical_seven_shapes=shapes,pair_matches=pairs,
   no_pair_deletion=True,no_added_pair_credit=True,no_six25_shape_match=True,no_added_six_credit=True))
 assert comparisons[0]['mean_increase']=='13/6'
 assert all(c['baseline_integer']==c['new_integer'] for c in comparisons)
 assert comparisons[1]['baseline_mean']==comparisons[1]['new_mean']
 assert comparisons[1]['baseline_range']==comparisons[1]['new_range']
 assert comparisons[1]['baseline_comparison']==comparisons[1]['new_comparison']
 assert all(s==[0,1,2,0,3,2,4] for s in obstructions[0]['canonical_seven_shapes'])
 assert len(obstructions[0]['pair_matches'])==4 and all(x['sum']==9 for x in obstructions[0]['pair_matches'])
 assert not obstructions[1]['pair_matches']
 out.update(baseline_comparison=comparisons,saved_cycle_obstructions=obstructions,
  initial_review_sha256=initial_hash,
  initial_checker_sha256=out['source_files_sha256'][Path(__file__).relative_to(R).as_posix()],
  supplement_method='Only already source-checked saved cycle rows and hash-identical result JSON were read. No graph array was loaded again.',
  supplement_completed_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
 sha(Path(__file__));PINS.pop(destination.relative_to(R).as_posix())
 out['source_files_sha256'].update(PINS)
 destination.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
 print(json.dumps(dict(status=out['status'],baseline_comparison=comparisons,saved_cycle_obstructions=obstructions),indent=2))

def add_zero_range_consequence(destination):
 previous_hash=sha(destination); out=read(destination)
 assert out['status']=='PASS_STATIC_AND_INDEPENDENT_SAVED_CYCLE_REVIEW'
 assert 'baseline_comparison' in out and 'single_pattern_consequence' not in out
 result=read(F/'results.json')
 assert PINS[(F/'results.json').relative_to(R).as_posix()]==out['source_files_sha256'][(F/'results.json').relative_to(R).as_posix()]
 rows=[]
 for p,threshold in zip(result['profiles'],[235,234]):
  obstruction=next(x for x in out['saved_cycle_obstructions'] if x['profile']==p['profile'])
  assert obstruction['no_six25_shape_match'] and obstruction['no_added_six_credit']
  z=Fraction(1098960*p['d']+8*p['p'],4200*p['d']+p['p'])
  assert str(z)==p['zero_range_comparison'] and z>threshold
  rows.append(dict(profile=p['profile'],unchanged_minimum=p['mean'],zero_range_comparison=str(z),
   excess_above_current_integer=str(z-threshold),next_integer_target=threshold-1,
   next_integer_target_unreachable_by_same_comparison=True))
 out['single_pattern_consequence']=dict(profiles=rows,
  statement='With every other hypothesis fixed, raising only the0123104 floor from25 upward leaves both attaining cycles and weights unchanged. Edge weights can only increase and edges can only be deleted. The old potentials remain valid, so the exact finite-graph minima stay488 and496. Even zero potential range cannot reach comparison integer targets234 and233.',
  method='Elementary monotonicity deduction from the checked saved cycles and exact rational comparison; no new graph calculation.',
  previous_review_sha256=previous_hash,previous_checker_sha256=out['source_files_sha256'][Path(__file__).relative_to(R).as_posix()])
 sha(Path(__file__));PINS.pop(destination.relative_to(R).as_posix());out['source_files_sha256'].update(PINS)
 destination.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
 print(json.dumps(out['single_pattern_consequence'],indent=2))

if __name__=='__main__':
 destination=H/'data/graph-review.json'
 if destination.exists():
  if 'baseline_comparison' in json.loads(destination.read_text()): add_zero_range_consequence(destination)
  else: add_saved_comparison(destination)
  raise SystemExit(0)
 out={}; start=time.monotonic()
 try: out,start=main()
 except Exception:
  out=dict(status='REVIEW_FAILED',error=traceback.format_exc())
 out.update(completed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-start,
  source_files_sha256=PINS)
 assert not destination.exists()
 destination.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
 print(json.dumps({k:v for k,v in out.items() if k!='source_files_sha256'},indent=2))
