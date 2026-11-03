"""Derive a next credit from two saved surviving cycles; no graph optimisation."""
from pathlib import Path
from fractions import Fraction
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
source=H/'data/five-cycle-zero/results.json';result=read(source)
oldpath=R/'milestones/121-replacement-window-pressure/data/pair-graph/results.json';old=read(oldpath)
rempath=H/'data/five-cycle-zero/removed-indices.json';removed=set(read(rempath))
current=next(x for x in result['profiles'] if x['profile']=='completed')['cycle']
oldcycle=next(x for x in old['profiles'] if x['profile']=='completed')['cycle']
def canon(ds):
 names={}
 return tuple(names.setdefault(x,len(names)) for x in ds)
def event(row):
 return canon(row['directions'][3:9])==(0,1,2,0,3,2) and row['counts'][2]<6 and row['counts'][4]<6 and row['counts'][2]+row['counts'][4]<=9
assert len(current)==7 and sum(x['weight'] for x in current)==3424
assert sum(event(row) for row in current)==2
assert len(oldcycle)==18 and all(row['edge'] not in removed for row in oldcycle)
assert not any(event(row) for row in oldcycle)
assert result['saved18_cycle_hypothetical_mean']=='3011/6' and result['saved18_checked_in']=='predecessor139'
mu=Fraction(3011,6);credit=(7*mu-3424)/2
threshold=235*(4200+mu)-1098960-8*mu-24*credit
assert credit==Fraction(533,12) and threshold==Fraction(5341,6)
ratio=(1098960+8*mu+24*credit)/(4200+mu)
out=dict(status='PASS_SAVED_CYCLE_ALGEBRA_ONLY',seven_cycle_edges=[x['edge'] for x in current],seven_cycle_weight=3424,seven_cycle_events=2,
 old18_edges=[x['edge'] for x in oldcycle],old18_survives=True,old18_events=0,old18_current_mean=str(mu),old18_mean_evidence='Pinned141 evaluator recomputed this sum under current shared charges before deletion; every old18 edge also survives the new deletion.',
 candidate_credit=str(credit),target_mean=str(mu),strict_range_threshold=str(threshold),zero_range_comparison=str(ratio),
 source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [source,oldpath,rempath,Path(__file__)]},
 scope='The seven-cycle upper cap is(3424+2C)/7 and the surviving zero-event18-cycle cap is3011/6. Their intersection choosesC533/12. Other cycles may have smaller means; no new potential or parameter optimum for the actual graph is claimed.')
path=H/'data/next-credit.json';assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:v for k,v in out.items() if k not in ['source_files_sha256','seven_cycle_edges','old18_edges']}))
