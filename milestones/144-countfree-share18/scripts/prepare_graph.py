"""Prepare a conditional impact test adding only012034 share18 to completed shares."""
from pathlib import Path
import ast,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'milestones/142-retuned-occurrence-credit/scripts/evaluate_graph.py'
assert sha(source)=='c057930ea46b47ad896105c37c668c01c60c235c738479d764c83a479d9b1208'
s=source.read_text(encoding='utf-8')
def change(a,b):
 global s
 assert s.count(a)==1,(a[:90],s.count(a));s=s.replace(a,b)
s=s.replace('SNAKE142_PARENT_PID','SNAKE144_GRAPH_PARENT_PID').replace('credit533-over12','share18-impact')
change("profiles = []\nfor name in ['completed']:","""# Change only the012034 count-free floor after every predecessor check.
share_shape=np.array([shape(word[-6:])==(0,1,2,0,3,4) for word in ds])[arrays['direction']]
last_count=digits[:,-1].astype(np.int64)
share_delta=np.where(share_shape,
    np.maximum(arrays['weight'],120*last_count+18)-np.maximum(arrays['weight'],120*last_count),0)
profile_base=base_weights['completed']+share_delta
assert np.all(profile_base[share_shape]==base_weights['conditional_floor18'][share_shape])
assert np.all(profile_base[~share_shape]==base_weights['completed'][~share_shape])
assert np.all(profile_base<=base_weights['conditional_floor18'])
for rel in ['milestones/144-countfree-share18/scripts/prepare_graph.py',
            'milestones/144-countfree-share18/data/graph-preparation.json',
            'milestones/144-countfree-share18/data/alternative-review.json']:
    pins[rel]=sha((ROOT/rel).read_bytes())
profiles = []
for name in ['completed']:""")
change('W = (12*(base_weights[name]+shared)+533*event)[mask]','W = (profile_base+shared)[mask]')
change('bound = Fraction(12*1098960*d+8*p+24*533*d+R,12*4200*d+p)','bound = Fraction(1098960*d+8*p+R,4200*d+p)')
change('weight_multiplier=12,occurrence_event=bool(event[k]),occurrence_credit_scaled=533*int(event[k]),','weight_multiplier=1,occurrence_event=bool(event[k]),occurrence_credit_scaled=0,\n            countfree_012034_bonus=int(share_delta[k]),')
change('row = dict(profile=name,mean=str(mu/12),scaled_mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,12*d)),cycle=cycle,',"row = dict(profile='completed_plus_012034_share18_pending',mean=str(mu),scaled_mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,")
s=s.replace("weight_multiplier=12,credit='533/12',occurrence_allowance=24,","weight_multiplier=1,credit='0',occurrence_allowance=24,")
change('target_mean_reached=mu/12>=Fraction(3011,6),target_range_reached=Fraction(R,12*d)<Fraction(5341,6),','target_mean_reached=mu>=496,target_range_reached=Fraction(R,d)<632,')
change('zero_range_comparison=str(Fraction(12*1098960*d+8*p+24*533*d,12*4200*d+p))','zero_range_comparison=str(Fraction(1098960*d+8*p,4200*d+p))')
change("print(name,'exact mean',mu/12,'range',Fraction(R,12*d),'conditional comparison',bound,flush=True)","print(name,'exact mean',mu,'range',Fraction(R,d),'conditional comparison',bound,flush=True)")
change('occurrence_events_retained=int(event[mask].sum()),weight_multiplier=12,','occurrence_events_retained=int(event[mask].sum()),weight_multiplier=1,')
change("credit='533/12',occurrence_allowance=24,","credit='0',occurrence_allowance=24,\n    added_share_floor=dict(shape=[0,1,2,0,3,4],floor=18,actual_lean_theorem_complete=False,changed_retained_edges=int(np.count_nonzero(share_delta[mask]))),")
change("inherited_hypotheses='All121 count-sum assumptions remain inherited; conditional_floor18 also retains its additional floor assumptions.',","inherited_hypotheses='All prior count-sum, hypothetical six-floor25 and odd-length pair assumptions remain. Only012034 share18 is added to completed shares; its actual Lean theorem remains pending. No other pending count-free floor is added.',")
change("scope='Exact finite-graph minima under stated hypotheses.","scope='The added012034 share18 is still a local hypothesis. Exact finite-graph minima under stated hypotheses.")
ast.parse(s)
assert "sha((3*(base_weights[name]+shared)+83*event)[mask].tobytes())==previous139_profiles[name]['weight_sha256']" in s
p=H/'scripts/evaluate_graph.py';assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n')
j=dict(status='PREPARED_NOT_RUN',hypothesis='Adding only012034 share18 may improve the completed-share graph comparison; other cycles may still obstruct234.',source_sha256=sha(source),prepare_sha256=sha(Path(__file__)),evaluate_sha256=sha(p),credit='0',weight_multiplier=1,added_share_floor=18,added_share_shape='012034',actual_lean_theorem_complete=False,retained_additional_profile='141 zero-credit full additional shares; unchanged.',scope='Conditional impact experiment. Complete share18 Lean checking and the remaining actual-snake assumptions are separate.')
(H/'data/graph-preparation.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(json.dumps(j))
