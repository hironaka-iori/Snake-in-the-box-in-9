"""Reuse the independent scalar row reconstruction for the new witness."""
from pathlib import Path
import ast
H=Path(__file__).resolve().parents[1];R=H.parents[1]
s=(R/'milestones/158-memory-bounded-floor-test/review/cycle-audit.py').read_text()
s=s.replace("base='milestones/158-memory-bounded-floor-test/'","base='milestones/164-loss-corrected-potential/'")
s=s.replace("data/floor17-complete/result.json","data/scaled-floor17/result.json")
s=s.replace("assert result['status']=='PASS_FIXED_MEAN_TARGET_OBSTRUCTION'","assert result['status'] in ['PASS_FIXED_MEAN_TARGET_OBSTRUCTION','PASS_MINIMUM_SCALED_RANGE_AT_MEAN4462']")
s=s.replace("assert len(full)==149\nassert sum(x['weight'] for x in full)==149*496-633", "assert sum(x['weight'] for x in full)*9 == sum(x['scaled_weight'] for x in walk)\nassert 4462*len(full)-9*sum(x['weight'] for x in full)==result['deficit_walk_value']")
s=s[:s.index('mu=Fraction(4462,9)')]+'''total=sum(x['weight'] for x in full)
deficit=4462*len(full)-9*total
assert all(saved['scaled_weight']==9*row['weight'] for saved,row in zip(walk,full))
assert 4462*9-9*3861==5409
assert 235*42262-(9*1098960+8*4462-180)==5414
output=dict(status='PASS_INDEPENDENT_SCALED_WALK_AUDIT', input_sha256=pins,
    verified_array_sha256=array_audit,selected_unique_rows=len(ids),
    walk=full,walk_length=len(full),walk_weight=total,scaled_deficit=deficit,
    target_range=5413,target_refuted=deficit>5413,
    old_nine_walk=old,cycle=cycle,cycle_total=4462,cycle_occurrences=cycle_events,
    new_global_bound=False,new_lean_check=False,
    audit_script_sha256=sha(Path(__file__)))
(H/'walk-audit.json').write_text(json.dumps(output,indent=2)+'\\n',encoding='utf-8')
print(json.dumps({key:output[key] for key in ['status','walk_length','walk_weight','scaled_deficit','target_refuted']}))
'''
ast.parse(s)
out=H/'review/walk-audit.py'
if out.exists():assert out.read_text()==s
else:out.write_text(s,encoding='utf-8',newline='\n')
