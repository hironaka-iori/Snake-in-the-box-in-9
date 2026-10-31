import importlib.util,json,random,statistics,sys,time
from pathlib import Path
from fractions import Fraction
from charge_fast import Geometry,Charges
HERE=Path(__file__).resolve().parent; ROOT=HERE.parent/'branch241-audit'; REPO=ROOT/'repo'
spec=importlib.util.spec_from_file_location('reference',ROOT/'global_extension/audit_charge.py');ref=importlib.util.module_from_spec(spec);spec.loader.exec_module(ref)
def compare(S,G):
 c=Charges(G,S);r=c.summary();old=ref.census(S,G.n)
 assert (r['T'],r['E2'],r['E3'],r['U'])==(old['T'],old['s0'],old['E3'],old['undominated_empty_squares'])
 assert Fraction(r['adaptive_sum_scaled'],G.A)==Fraction(old['adaptive_score_sum'])
 assert Fraction(r['uniform_sum_scaled'],G.G)==Fraction(old['uniform_score_sum'])
 return c
start=time.perf_counter();control=0;G3=Geometry(3)
for mask in range(256):
 S=[v for v in range(8) if mask>>v&1]
 if any(mask&m==m for m,*_ in G3.squares):continue
 compare(S,G3);control+=1
G4=Geometry(4);rng=random.Random(241234);random4=0
while random4<300:
 S=[v for v in range(16) if rng.randrange(3)==0]
 if any(G4.mask(S)&m==m for m,*_ in G4.squares):continue
 compare(S,G4);random4+=1
G=Geometry(9);bank=json.loads((REPO/'work/bank9.json').read_text());path=bank[67]['vertex_sequence'];c=compare(path,G)
for v in reversed(path[175:]):
 c.remove(v);p=path[:c.S.bit_count()];fresh=Charges(G,p)
 assert c.a==fresh.a and c.g==fresh.g and c.summary()==fresh.summary()
for name in ('adversary208','adversary224'):
 data=json.loads((REPO/f'milestones/11-local-ceiling/data/{name}.json').read_text());compare(data['S'],G)
oldtimes=[];newtimes=[]
for _ in range(7):
 t=time.perf_counter();ref.census(path,9);oldtimes.append(time.perf_counter()-t)
 t=time.perf_counter();Charges(G,path).summary();newtimes.append(time.perf_counter()-t)
# Same prefix sequence, fresh versus incremental, excluding geometry setup in both.
fresh_times=[];inc_times=[]
for _ in range(3):
 t=time.perf_counter()
 for v in range(180,len(path)+1):Charges(G,path[:v])
 fresh_times.append(time.perf_counter()-t)
 t=time.perf_counter();c=Charges(G,path)
 for v in reversed(path[180:]):c.remove(v)
 inc_times.append(time.perf_counter()-t)
r={'reference_Q3_subsets_without_4cycle':control,'reference_random_Q4_sets':random4,'Q9_reference_datasets':3,'incremental_tail_removals_checked':len(path)-175,'exact_agreement':True,'adaptive_scale_Q9':G.A,'uniform_scale_Q9':G.G,'old_seconds_median':statistics.median(oldtimes),'new_seconds_median':statistics.median(newtimes),'fresh_prefix_seconds_median':statistics.median(fresh_times),'incremental_prefix_seconds_median':statistics.median(inc_times),'geometry_setup_included':False,'total_validation_seconds':time.perf_counter()-start}
r['census_speedup']=r['old_seconds_median']/r['new_seconds_median'];r['prefix_scan_speedup']=r['fresh_prefix_seconds_median']/r['incremental_prefix_seconds_median'];(HERE/'validation.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))

