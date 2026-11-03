"""Independent bounded result review. No graph search or all-edge potential scan.
Run only after the parent confirms that the graph process is terminal.
"""
from pathlib import Path
from fractions import Fraction
import argparse, ast, datetime, gc, gzip, hashlib, json, subprocess, time, traceback, zipfile
import numpy as np
H=Path(__file__).resolve().parents[1]; ROOT=H.parents[1]; F=H/'data/exclusion-credit83'; PINS={}

def sha(path):
 path=Path(path); h=hashlib.sha256()
 with path.open('rb') as stream:
  for block in iter(lambda:stream.read(1048576),b''):h.update(block)
 value=h.hexdigest(); PINS[path.relative_to(ROOT).as_posix()]=value; return value
def read(path):
 sha(path); return json.loads(Path(path).read_text(encoding='utf-8-sig'))
def canon(word):
 names={}; return tuple(names.setdefault(int(x),len(names)) for x in word)
def shape(word):return min(canon(word),canon(word[::-1]))

def main():
 run=read(F/'run-status.json'); assert run['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA' and run['returncode']==0
 result=read(F/'results.json'); assert result['status']==run['status']; sha(Path(__file__))
 prep=read(H/'data/preparation.json'); evaluator=H/'scripts/evaluate_graph.py'; generator=H/'scripts/prepare_graph.py'
 assert sha(evaluator)==prep['evaluate_sha256']==run['script_sha256']==result['script_sha256']
 assert sha(generator)==prep['prepare_sha256']
 assert sha(ROOT/'milestones/131-odd-pair-six-count/scripts/evaluate_graph.py')==prep['source_sha256']
 assert sha(F/'evaluate_graph.exact.py')==sha(evaluator)
 ast.parse(evaluator.read_text(encoding='utf-8-sig')); ast.parse(generator.read_text(encoding='utf-8-sig'))
 for rel,digest in result['source_files_sha256'].items():assert sha(ROOT/rel)==digest,rel
 for resources in [run['resources'],read(F/'worker-resources.json')]:
  assert resources['free_bytes']>=3*1024**3 and not resources['other_fullgraph_processes']
 algorithm=subprocess.check_output(['git','show','41797e3863e17be730f06e3a9c5df09bbc0d404d:milestones/10-window-aggregate/scripts/refine.py'],cwd=ROOT).decode().replace('\r\n','\n')
 assert hashlib.sha256(algorithm.encode()).hexdigest()==result['algorithm_sha256']
 assert result['coefficients']==[24]*5 and result['weight_multiplier']==3 and result['credit']=='83/3'
 assert result['occurrence_allowance']==24 and result['odd_length_pair_floor']==9
 assert result['six_count_hypothesis']['floor']==25 and not result['six_count_hypothesis']['lean_proof_complete']
 assert result['shared_bonus_is_maximum'] and result['old_bonus_preserved'] and result['predecessor131_reproduced']
 assert result['baseline121_weight_hashes_reproduced'] and result['baseline121_removals_reproduced']
 previous=read(ROOT/'milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json')
 older=read(ROOT/'milestones/121-replacement-window-pressure/data/pair-graph/results.json')
 saved18=next(p['cycle'] for p in older['profiles'] if p['profile']=='completed'); assert len(saved18)==18
 old_removed=np.asarray(read(ROOT/'milestones/131-odd-pair-six-count/data/odd-pair9-six25/removed-indices.json'),dtype=np.int64)
 new_removed=np.asarray(read(F/'removed-indices.json'),dtype=np.int64)
 assert np.all(old_removed[1:]>old_removed[:-1]) and np.all(new_removed[1:]>new_removed[:-1])
 assert np.isin(old_removed,new_removed,assume_unique=True).all()
 added=np.setdiff1d(new_removed,old_removed,assume_unique=True)
 chosen={int(e['edge']) for p in result['profiles']+previous['profiles'] for e in p['cycle']}
 chosen|={int(e['edge']) for e in saved18}|set(map(int,added)); selected=np.asarray(sorted(chosen),dtype=np.int64)
 rows={int(k):{} for k in selected}
 meta=read(ROOT/'milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
 ds=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
 completed=read(ROOT/'milestones/73-countfree-share-catalogue/data/proved-model.json')
 floors={tuple(x['shape']):x['share'] for x in completed['countfree_floors']}
 extra={(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
 graph=ROOT/'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
 with zipfile.ZipFile(graph) as archive:assert max(i.file_size for i in archive.infolist())<150000000
 target_code=sum((v-1)*6**(5-i) for i,v in enumerate([6,3,3,3,5,2]))
 base_lookup=np.asarray([canon(w)==(0,1,2,3,0,1,4,3,0) for w in ds])
 suffix_lookup=np.asarray([shape(w[3:9])==(0,1,2,0,3,2) for w in ds]); largest=0; order=[]
 with np.load(graph) as archive:
  names=['direction','count_code']+[x for x in archive.files if x not in ['direction','count_code']]
  assert set(names)==set(meta['arrays_sha256'])
  for name in names:
   a=archive[name]; assert a.ndim==1 and a.nbytes<150000000
   assert hashlib.sha256(memoryview(a)).hexdigest()==meta['arrays_sha256'][name]
   largest=max(largest,a.nbytes); order.append(name)
   if name=='direction':
    original_edges=len(a); assert np.all(a[1:]>=a[:-1]); base_directions=base_lookup[a]; suffix_directions=suffix_lookup[a]
   else:assert len(a)==original_edges
   for k,value in zip(selected,a[selected]):rows[int(k)][name]=int(value)
   if name=='count_code':
    assert np.all((0<=a)&(a<6**6)); base_mask=base_directions&(a==target_code)
    x=a//6**3%6+1; y=a//6%6+1; event_mask=suffix_directions&(x<6)&(y<6)&(x+y<=9)
    retained=np.ones(original_edges,dtype=bool); retained[old_removed]=False
    assert int(retained.sum())==previous['edges']==result['predecessor131_edges']
    assert int(base_mask.sum())==result['new_full_nine_rejections_total']
    assert np.array_equal(np.flatnonzero(base_mask&retained),added)
    assert len(added)==result['new_full_nine_rejections_on_predecessor']
    retained&=~base_mask; assert np.array_equal(np.flatnonzero(~retained),new_removed)
    assert int(retained.sum())==result['edges']
    assert int((event_mask&retained).sum())==result['occurrence_events_retained']
    assert not np.any(event_mask&retained&~(((x==4)&(y==5))|((x==5)&(y==4))))
    del base_directions,suffix_directions,base_mask,event_mask,retained,x,y
   del a; gc.collect()

 def evaluate(k,profile):
  a=rows[k]; w=ds[a['direction']]; c=[a['count_code']//6**j%6+1 for j in range(5,-1,-1)]; credit=0
  for rule in result['rules']:
   word,five,target=w[3:9],c[1:6],shape(rule['directions'])
   if shape(word)!=target:continue
   if canon(word)!=target:five=five[::-1]
   if all(x>=lo and (21 if x==6 else x)<=hi for x,(lo,hi) in zip(five,rule['bounds'])):
    credit=max(credit,24*max(0,rule['lower']-sum(five[j] for j in rule['positions'])))
  pair=24*max(0,9-c[2]-c[4]) if shape(w[3:9])==(0,1,2,0,3,2) else 0
  match=shape(w[2:])==shape([0,1,2,3,1,0,4]); guard=match and c[0]<6
  six=24*max(0,25-sum(c)) if guard else 0; fs=floors if profile=='completed' else floors|extra
  base=max(a['weight'],120*c[-1]+fs.get(shape(w[-6:]),0)); shared=max(credit,pair,six)
  event=shape(w[3:9])==(0,1,2,0,3,2) and c[2]<6 and c[4]<6 and c[2]+c[4]<=9
  reject=canon(w)==(0,1,2,3,0,1,4,3,0) and c==[6,3,3,3,5,2]
  row=dict(edge=k,u=a['U'],v=a['V'],direction=a['direction'],history=a['history'],count_code=a['count_code'],directions=w,counts=c,base_weight=base,old_bonus24=credit,pair_bonus24=pair,six_bonus24=six,shared_bonus=shared,weight=3*(base+shared)+83*int(event),six_shape_matches=match,six_guard=guard,weight_multiplier=3,occurrence_event=bool(event),occurrence_credit_scaled=83*int(event))
  return row,base+shared,reject

 for p in previous['profiles']:
  for e in p['cycle']:
   row,old_weight,_=evaluate(e['edge'],p['profile'])
   assert all((old_weight if key=='weight' else row[key])==value for key,value in e.items())
 profiles=[]; assert {p['profile'] for p in result['profiles']}=={'completed','conditional_floor18'}
 for p in result['profiles']:
  assert read(F/(p['profile']+'-profile.json'))==p; rebuilt=[]
  for e in p['cycle']:
   row,_,reject=evaluate(e['edge'],p['profile']); assert not reject and row==e
   assert not np.isin(e['edge'],new_removed); rebuilt.append(row)
  assert rebuilt and all(e['v']==rebuilt[(i+1)%len(rebuilt)]['u'] for i,e in enumerate(rebuilt))
  scaled=Fraction(sum(e['weight'] for e in rebuilt),len(rebuilt))
  assert str(scaled)==p['scaled_mean'] and str(scaled/3)==p['mean']
  assert (scaled.numerator,scaled.denominator)==(p['p'],p['d'])
  assert p['weight_multiplier']==3 and p['credit']=='83/3' and p['occurrence_allowance']==24
  assert p['potential_file']==p['profile']+'-potential.i64.gz'; potpath=F/p['potential_file']; sha(potpath)
  raw=gzip.decompress(potpath.read_bytes()); assert hashlib.sha256(raw).hexdigest()==p['potential_sha256']
  assert len(raw)==8*result['states']==8*meta['states']; potential=np.frombuffer(raw,dtype='<i8')
  assert int(potential.min())==0 and int(potential.max())==p['range_scaled']
  assert str(Fraction(p['range_scaled'],3*p['d']))==p['range']
  slacks=[p['d']*e['weight']+int(potential[e['u']])-p['p']-int(potential[e['v']]) for e in rebuilt]
  assert all(x==0 for x in slacks)
  assert p['all_edge_inequalities_checked'] and p['inequalities_checked']==result['edges']
  assert p['minimum_slack']==0 and p['cycle_attaining'] and 1<=p['iterations']<=1500
  den=3*4200*p['d']+p['p']; num=3*1098960*p['d']+8*p['p']+24*83*p['d']
  bound=Fraction(num+p['range_scaled'],den)
  assert str(bound)==p['comparison_bound'] and bound.numerator//bound.denominator==p['comparison_integer_bound']
  assert str(Fraction(num,den))==p['zero_range_comparison']
  assert p['target_mean_reached']==(scaled/3>=Fraction(3011,6))
  assert p['target_range_reached']==(Fraction(p['range_scaled'],3*p['d'])<Fraction(7753,6))
  profiles.append(dict(profile=p['profile'],mean=str(scaled/3),scaled_mean=str(scaled),cycle_length=len(rebuilt),cycle_events=sum(e['occurrence_event'] for e in rebuilt),cycle_weights=[e['weight'] for e in rebuilt],cycle_slacks=slacks,potential_length=len(potential),range_scaled=p['range_scaled'],range=p['range'],comparison=str(bound),comparison_integer=p['comparison_integer_bound']))
  del potential,raw; gc.collect()
 check18=[evaluate(e['edge'],'completed') for e in saved18]
 assert all(not rejected and not row['occurrence_event'] for row,_,rejected in check18)
 assert Fraction(sum(row['weight'] for row,_,_ in check18),54)==Fraction(3011,6)
 assert result['saved18_cycle_hypothetical_mean']=='3011/6'
 for name in ['stdout.log','stderr.log']:sha(F/name)
 assert all(sha(ROOT/rel)==digest for rel,digest in list(PINS.items()))
 return dict(status='PASS_INDEPENDENT_SAVED_RESULT_REVIEW',profiles=profiles,original_edges=original_edges,predecessor_edges=previous['edges'],retained_edges=result['edges'],newly_removed_edges=list(map(int,added)),new_mask_and_event_counts_independently_checked=True,selected_source_rows=len(rows),source_array_hashes_verified=True,npz_member_order=order,each_npz_member_read_once=True,largest_array_bytes=largest,saved18_mean='3011/6',source_and_run_pins_verified=True,all_edge_inequalities_independently_recomputed=False,all_edge_status='Producer reports an all-edge check; this review checked only saved cycle slacks.',limitations=['No independent all-edge potential scan or minimum-cycle search.','Inherited odd-length and hypothetical count/share-floor assumptions remain.','Even-length conclusions and the full graph-to-snake comparison are not automatic.','This review establishes no new actual-snake upper bound.'])

if __name__=='__main__':
 parser=argparse.ArgumentParser(); parser.add_argument('--graph-terminal-confirmed',action='store_true',required=True); parser.parse_args()
 started=time.monotonic()
 try:output=main()
 except BaseException as error:output=dict(status='FAIL_INDEPENDENT_SAVED_RESULT_REVIEW',error=repr(error),traceback=traceback.format_exc(),all_edge_inequalities_independently_recomputed=False)
 output.update(completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-started,source_files_sha256=PINS)
 destination=H/'data/result-review.json'
 if destination.exists():
  old=json.loads(destination.read_text(encoding='utf-8-sig')); output['prior_attempts']=old.get('prior_attempts',[])+[{k:v for k,v in old.items() if k!='prior_attempts'}]
 destination.write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
 lines=['# Independent saved-result review','','Status: `'+output['status']+'`.','']
 if output['status'].startswith('PASS_'):
  lines+=['Both saved cycles were rebuilt from original source-array rows with exact credit and scaling checks. The new deletion and retained event counts were checked independently from direction/count-code attributes. Potential hashes, lengths, ranges, and saved-cycle zero slacks were checked. No independent all-edge potential scan or graph search was performed.','','| Profile | Original mean | Original range | Cycle length | Credited events | Exact comparison | Integer part |','|---|---|---|---:|---:|---|---:|']
  for p in output['profiles']:lines.append(f"| {p['profile']} | {p['mean']} | {p['range']} | {p['cycle_length']} | {p['cycle_events']} | {p['comparison']} | {p['comparison_integer']} |")
  lines+=['',f"Newly removed source edges: {output['newly_removed_edges']}. Each original NPZ member was read once; the largest array held {output['largest_array_bytes']} bytes.",'','All source pins and detailed checks are recorded in `data/result-review.json`. The producer reports the full all-edge certificate; this independent review checks saved cycle slacks only.','','The inherited odd-length restrictions and hypothetical local floors remain. The actual-snake graph and charge assembly remain separate obligations. No new actual-snake upper bound is claimed.']
 else:lines+=['The review failed; the error and any prior attempts are preserved in `data/result-review.json`.',output['error']]
 (H/'audit/result-review.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')
 print(json.dumps({k:v for k,v in output.items() if k not in ['source_files_sha256','prior_attempts']},indent=2))
 raise SystemExit(0 if output['status'].startswith('PASS_') else 1)
