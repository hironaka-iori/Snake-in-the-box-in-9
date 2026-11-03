"""Derive the zero-credit experiment from the pinned, proof-gated140 evaluator."""
from pathlib import Path
from fractions import Fraction
import ast,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=R/'milestones/140-five-cycle-window/scripts/evaluate_graph.py'
assert sha(source)=='ef83027eb70f0c2dd2a6e519d2cee78bcfe72e1559b6c04134d51dd5f55e6b42'
s=source.read_text(encoding='utf-8')
def change(old,new):
 global s
 assert s.count(old)==1,(old[:100],s.count(old))
 s=s.replace(old,new)
s=s.replace('SNAKE140_PARENT_PID','SNAKE141_PARENT_PID').replace('five-cycle-credit83','five-cycle-zero')
change("completion_path = _home / 'data/proof-completion.json'", "proof_home = _home.parent / '140-five-cycle-window'\n    completion_path = proof_home / 'data/proof-completion.json'")
s=s.replace('source.relative_to(_home.resolve())','source.relative_to(proof_home.resolve())').replace('receipt.relative_to(_home.resolve())','receipt.relative_to(proof_home.resolve())')
change('W = (3*(base_weights[name]+shared)+83*event)[mask]', 'W = (base_weights[name]+shared)[mask]')
change('bound = Fraction(3*1098960*d+8*p+24*83*d+R,3*4200*d+p)', 'bound = Fraction(1098960*d+8*p+R,4200*d+p)')
change('weight_multiplier=3,occurrence_event=bool(event[k]),occurrence_credit_scaled=83*int(event[k]),', 'weight_multiplier=1,occurrence_event=bool(event[k]),occurrence_credit_scaled=0,')
change("row = dict(profile=name,mean=str(mu/3),scaled_mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,3*d)),cycle=cycle,", "row = dict(profile=name,mean=str(mu),scaled_mean=str(mu),p=p,d=d,range_scaled=R,range=str(Fraction(R,d)),cycle=cycle,")
change("weight_multiplier=3,credit='83/3',occurrence_allowance=24,", "weight_multiplier=1,credit='0',occurrence_allowance=24,")
change('target_mean_reached=mu/3>=Fraction(3011,6),target_range_reached=Fraction(R,3*d)<Fraction(7753,6),', 'target_mean_reached=mu>=496,target_range_reached=Fraction(R,d)<632,')
change('zero_range_comparison=str(Fraction(3*1098960*d+8*p+24*83*d,3*4200*d+p))', 'zero_range_comparison=str(Fraction(1098960*d+8*p,4200*d+p))')
change("print(name,'exact mean',mu/3,'range',Fraction(R,3*d),'conditional comparison',bound,flush=True)", "print(name,'exact mean',mu,'range',Fraction(R,d),'conditional comparison',bound,flush=True)")
change('occurrence_events_retained=int(event[mask].sum()),weight_multiplier=3,', 'occurrence_events_retained=int(event[mask].sum()),weight_multiplier=1,')
change("credit='83/3',occurrence_allowance=24,", "credit='0',occurrence_allowance=24,")
change("pins.update(_proof_gate_info['pins'])", "pins.update(_proof_gate_info['pins'])\nfor extra in ['milestones/141-zero-credit-comparison/scripts/prepare_graph.py','milestones/141-zero-credit-comparison/data/preparation.json']:\n    pins[extra]=sha((ROOT/extra).read_bytes())")
# The predecessor must still use the old multiplier and credit when hashes are compared.
assert "sha((3*(base_weights[name]+shared)+83*event)[mask].tobytes())==previous139_profiles[name]['weight_sha256']" in s
assert s.count('83*event')==2 # predecessor weight reconstruction and old four-cycle comparison
ast.parse(s)
p=H/'scripts/evaluate_graph.py';assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n')
for num,den,ran in [(496,1,602),(2446,5,2973),(500,1,620)]:
 mu=Fraction(num,den);rr=Fraction(ran,den)
 assert (1098960+8*mu+rr)/(4200+mu)==Fraction(1098960*den+8*num+ran,4200*den+num)
proof=R/'milestones/140-five-cycle-window/data/proof-completion.json';j=json.loads(proof.read_text())
assert j['status']=='PASS_ACTUAL_012032_WEAK_EXCLUSION'
out=dict(status='PREPARED_NOT_RUN',hypothesis='With zero occurrence credit after the checked weak exclusion, the additional-share profile may retain mean496 with range below632. Test both profiles; no global bound is implied.',source_sha256=sha(source),prepare_sha256=sha(Path(__file__)),evaluate_sha256=sha(p),proof_completion_sha256=sha(proof),credit='0',weight_multiplier=1,profiles=['completed','conditional_floor18'],predecessor139_weight_reconstruction_unchanged=True,scope='Preparation and exact algebra only. Inherited count and share hypotheses, odd-length restriction and graph-to-snake obligations remain.')
(H/'data/preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out))
