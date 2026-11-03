"""Preserve the zero-credit experiment; prepare one cycle-selected credit test."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
src=H/'scripts/evaluate_graph.py';s=src.read_text()
def change(a,b):
 global s
 assert a in s,a
 s=s.replace(a,b)
change("default='share18-impact'","default='share18-credit601-over36'")
change("args.label or 'share18-impact'","args.label or 'share18-credit601-over36'")
change("evaluate_(graph|pair|six_shapes)","evaluate_(graph|pair|six_shapes|retuned)")
change("W = (profile_base+shared)[mask]","W = (36*(profile_base+shared)+601*event)[mask]")
change("bound = Fraction(1098960*d+8*p+R,4200*d+p)","bound = Fraction(1098960*36*d+8*p+24*601*d+R,4200*36*d+p)")
change("weight_multiplier=1,occurrence_event=bool(event[k]),occurrence_credit_scaled=0,","weight_multiplier=36,occurrence_event=bool(event[k]),occurrence_credit_scaled=601,")
change("mean=str(mu),scaled_mean=str(mu)","mean=str(mu/36),scaled_mean=str(mu)")
change("range=str(Fraction(R,d))","range=str(Fraction(R,36*d))")
change("weight_multiplier=1,credit='0'","weight_multiplier=36,credit='601/36'")
change("target_mean_reached=mu>=496,target_range_reached=Fraction(R,d)<632,","target_mean_reached=mu/36>=496,target_range_reached=bound<235,")
change("zero_range_comparison=str(Fraction(1098960*d+8*p,4200*d+p))","zero_range_comparison=str(Fraction(1098960*36*d+8*p+24*601*d,4200*36*d+p))")
change("'exact mean',mu,'range',Fraction(R,d)","'exact mean',mu/36,'range',Fraction(R,36*d)")
change("weight_multiplier=1,\n    credit='0'","weight_multiplier=36,\n    credit='601/36'")
change("'milestones/144-countfree-share18/data/alternative-review.json']:","'milestones/144-countfree-share18/data/alternative-review.json',\n            'milestones/144-countfree-share18/scripts/prepare_retuned.py',\n            'milestones/144-countfree-share18/data/cycle-analysis.json']:")
change("Only012034 share18 is added to completed shares;","Only012034 share18 is added to completed shares and existing occurrence credit is601/36;")
target=H/'scripts/evaluate_retuned.py';assert not target.exists();target.write_text(s,encoding='utf-8',newline='\n')
record=dict(status='PREPARED_NOT_RUN',credit='601/36',selection='Exact feasible two-cycle parameters, not a full-graph prediction',
 source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),generated_sha256=hashlib.sha256(target.read_bytes()).hexdigest())
(H/'data/retuned-preparation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
