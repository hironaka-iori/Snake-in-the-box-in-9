"""Select a verified native certificate for each premise of the mixed target."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];read=lambda p:json.loads(p.read_text())
audit=read(HERE/'data/native-audit.json');assert audit['status']=='PASS_NATIVE_FORMULA_AUDIT'
shapes=read(HERE/'data/all-six-direction-shapes.json')['up_to_reversal']
need=[16]*9;need[2]=20;need[5]=12;selected=[]
for i,bound in enumerate(need):
 candidates=[]
 for r in audit['certificates']:
  if r['shape_index']==i and r['share_lower']>=bound:
   tag=r['certificate'].removesuffix('-certificate.json');p=HERE/f'build/{tag}.drat'
   candidates.append((p.stat().st_size,r))
 assert candidates,i
 size,row=min(candidates,key=lambda x:x[0])
 selected.append(dict(directions=shapes[i],required_share=bound,certificate=row['certificate'],proved_cnf_share=row['share_lower'],drat_bytes=size,cycle_cuts=row['cycle_cuts'],core_clauses=row['core_clauses']))
verification=HERE/'data/countfree16-all-except012034x20-except012310x12-verification.json';v=read(verification)
assert v['status']=='PASS_EXACT_CONDITIONAL_MODEL' and v['mean']=='496' and v['potential_range']==600 and v['conditional_integer_bound']==234
uniform=[]
for i in range(9):
 candidates=[r for r in audit['certificates'] if r['shape_index']==i and r['share_lower']>=16]
 if not candidates:break
 row=min(candidates,key=lambda r:(HERE/'build'/r['certificate'].replace('-certificate.json','.drat')).stat().st_size)
 uniform.append(dict(shape_index=i,certificate=row['certificate'],drat_bytes=(HERE/'build'/row['certificate'].replace('-certificate.json','.drat')).stat().st_size))
out=dict(status='ALL_NINE_NATIVE_PREMISES_VERIFIED',selected=selected,drat_total_bytes=sum(x['drat_bytes'] for x in selected),uniform_share16=uniform,uniform_complete=len(uniform)==9,uniform_drat_total_bytes=sum(x['drat_bytes'] for x in uniform),finite_model_verification_sha256=hashlib.sha256(verification.read_bytes()).hexdigest(),conditional_integer_bound=234,scope='All required Boolean refutations are independently checked. Nine arbitrary-snake geometric/Lean share proofs, reversal normalization, the global coreShare/shareN connection and complete graph interpretation remain outstanding. No new unconditional upper bound.')
(HERE/'data/portfolio.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
