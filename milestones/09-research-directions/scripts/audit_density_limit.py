"""Recompute the bank witness supporting the uniform-density method limit."""
import hashlib
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[3]/'work'))
from audit_square_counts import audit
from check_snake import verify

bank_path=Path('work/bank9.json')
row=json.loads(bank_path.read_text())[130]
vertices=row['vertex_sequence']
checked=verify([(a^b).bit_length()-1 for a,b in zip(vertices,vertices[1:])])
assert checked['edges']==191
result=audit(vertices)
assert result['square_counts'][1]==1632
result.update(bank_index=130,bank_sha256=hashlib.sha256(bank_path.read_bytes()).hexdigest(),vertex_sequence=vertices,
    arithmetic_census={'vertices':211,'empty':17,'singleton':1795,'double':2587,'triple':209},
    scope='Witness and square census checked in Python. The abstract arithmetic and endpoint-budget lemmas are separately checked in Lean; this witness census is not yet connected to them in Lean.')
output=Path('milestones/09-research-directions/data');output.mkdir(exist_ok=True)
(output/'density_limit_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print({key:result[key] for key in ['vertices','square_counts','bank_index','scope']})
