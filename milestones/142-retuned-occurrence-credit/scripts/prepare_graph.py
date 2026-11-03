"""Test credit533/12 on completed shares while retaining141's zero-credit alternative."""
from pathlib import Path
from fractions import Fraction
import ast,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'milestones/141-zero-credit-comparison/scripts/evaluate_graph.py'
assert sha(source)=='7099cb809feb6720ac64c91b760681d4dd9ad2589995691bc43d82d76daf0b4c'
s=source.read_text(encoding='utf-8')
def change(old,new):
 global s
 assert s.count(old)==1,(old[:100],s.count(old))
 s=s.replace(old,new)
s=s.replace('SNAKE141_PARENT_PID','SNAKE142_PARENT_PID').replace('five-cycle-zero','credit533-over12')
change('ids = np.flatnonzero(mask)',"""# Reproduce the immediate zero-credit predecessor before changing weights.
previous141=read('milestones/141-zero-credit-comparison/data/five-cycle-zero/results.json')
assert previous141['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
previous141_profiles={p['profile']:p for p in previous141['profiles']}
previous141_removed=read('milestones/141-zero-credit-comparison/data/five-cycle-zero/removed-indices.json')
assert np.array_equal(np.flatnonzero(~mask),np.array(previous141_removed))
assert int(mask.sum())==previous141['edges']
for name in ['completed','conditional_floor18']:
    assert sha((base_weights[name]+shared)[mask].tobytes())==previous141_profiles[name]['weight_sha256']
for rel in ['milestones/142-retuned-occurrence-credit/scripts/prepare_graph.py',
            'milestones/142-retuned-occurrence-credit/data/preparation.json',
            'milestones/141-zero-credit-comparison/data/next-credit.json',
            'milestones/141-zero-credit-comparison/data/Comparison141-audit.json']:
    pins[rel]=sha((ROOT/rel).read_bytes())
seven_ids=np.array([e['edge'] for e in previous141_profiles['completed']['cycle']])
assert np.all(mask[seven_ids]) and len(seven_ids)==7 and int(event[seven_ids].sum())==2
assert Fraction(int((12*(base_weights['completed']+shared)+533*event)[seven_ids].sum()),12*7)==Fraction(3011,6)

ids = np.flatnonzero(mask)""")
change('assert np.all(previous139_mask[saved_ids])', 'assert np.all(previous139_mask[saved_ids])\nassert np.all(mask[saved_ids])')
change("profiles = []\nfor name in ['completed','conditional_floor18']:", "profiles = []\nfor name in ['completed']:")
change('W = (base_weights[name]+shared)[mask]', 'W = (12*(base_weights[name]+shared)+533*event)[mask]')
change('bound = Fraction(1098960*d+8*p+R,4200*d+p)', 'bound = Fraction(12*1098960*d+8*p+24*533*d+R,12*4200*d+p)')
change('weight_multiplier=1,occurrence_event=bool(event[k]),occurrence_credit_scaled=0,', 'weight_multiplier=12,occurrence_event=bool(event[k]),occurrence_credit_scaled=533*int(event[k]),')
change('row = dict(profile=name,mean=str(mu),scaled_mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,', 'row = dict(profile=name,mean=str(mu/12),scaled_mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,12*d)),cycle=cycle,')
change("weight_multiplier=1,credit='0',occurrence_allowance=24,", "weight_multiplier=12,credit='533/12',occurrence_allowance=24,")
change('target_mean_reached=mu>=496,target_range_reached=Fraction(R,d)<632,', 'target_mean_reached=mu/12>=Fraction(3011,6),target_range_reached=Fraction(R,12*d)<Fraction(5341,6),')
change('zero_range_comparison=str(Fraction(1098960*d+8*p,4200*d+p))', 'zero_range_comparison=str(Fraction(12*1098960*d+8*p+24*533*d,12*4200*d+p))')
change("print(name,'exact mean',mu,'range',Fraction(R,d),'conditional comparison',bound,flush=True)", "print(name,'exact mean',mu/12,'range',Fraction(R,12*d),'conditional comparison',bound,flush=True)")
change('occurrence_events_retained=int(event[mask].sum()),weight_multiplier=1,', 'occurrence_events_retained=int(event[mask].sum()),weight_multiplier=12,')
change("credit='0',occurrence_allowance=24,", "credit='533/12',occurrence_allowance=24,")
change('predecessor139_reproduced=True,predecessor139_edges=int(previous139_mask.sum()),', "predecessor139_reproduced=True,predecessor139_edges=int(previous139_mask.sum()),\n    predecessor141_reproduced=True,predecessor141_edges=previous141['edges'],\n    retained_additional_profile_source='milestones/141-zero-credit-comparison/data/five-cycle-zero/results.json',")
ast.parse(s)
assert "sha((3*(base_weights[name]+shared)+83*event)[mask].tobytes())==previous139_profiles[name]['weight_sha256']" in s
p=H/'scripts/evaluate_graph.py';assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n')
for p0,d0,rr in [(6022,1,10681),(6000,1,9000),(3424,7,4159)]:
 mu=Fraction(p0,12*d0);ran=Fraction(rr,12*d0)
 assert (1098960+8*mu+24*Fraction(533,12)+ran)/(4200+mu)==Fraction(12*1098960*d0+8*p0+24*533*d0+rr,12*4200*d0+p0)
out=dict(status='PREPARED_NOT_RUN',hypothesis='Credit533/12 may let the completed-share profile attain mean3011/6 with range<5341/6; another cycle or excessive range may refute this.',source_sha256=sha(source),prepare_sha256=sha(Path(__file__)),evaluate_sha256=sha(p),credit='533/12',weight_multiplier=12,profiles=['completed'],retained_additional_profile='141 zero credit, mean496, range602, comparison551765/2348',target_scaled_mean=6022,target_strict_scaled_range=10682,scope='Exact preparation and arithmetic only. All inherited hypotheses and proof boundaries remain unchanged.')
(H/'data/preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
