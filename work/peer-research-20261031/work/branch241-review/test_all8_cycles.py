from all8_cycles import templates,validate_cycle,enumerate_all8
import json
from pathlib import Path
C=templates()[0];assert validate_cycle(C,4)
negative=[([v+16 for v in C],4),([-v-1 for v in C],4),([float(v) for v in C],4),([True]+list(C[1:]),4),(C,0),(C,4.0),(C,True)]
rejected=0
for cycle,n in negative:
 try:validate_cycle(cycle,n)
 except ValueError:rejected+=1
 else:raise AssertionError((cycle,n))
for domain,n in [([True],9),([512],9),([0],4.0),([0],True)]:
 try:enumerate_all8(domain,n)
 except ValueError:rejected+=1
 else:raise AssertionError((domain,n))
cycles,meta=enumerate_all8(range(16),4);assert set(cycles)==set(templates())
result={'valid_Q4_template':True,'malformed_inputs_rejected':rejected,'exhaustive_Q4_embeddings':len(cycles)}
(Path(__file__).parent/'all8_input_hardening.json').write_text(json.dumps(result,indent=2));print(result)
