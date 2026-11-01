"""Export OFF=8192 proof data; generated checker soundness must be checked in Lean."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];OUT=HERE/'share-proof'
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
import gen_checker_variants as v
import gen_lean_lrat as g
base=ROOT/'work/final_lean/LratCheck.lean';fast=ROOT/'work/final_lean/LratFast.lean'
s=v.variant(base.read_text(),13,8192,'LratO8k','LratFast','LocalWindowModel')
s+='\n#print axioms Snake9.LratO8k.rawMask_true\n#print axioms Snake9.LratO8k.start_true\n'
(OUT/'lean/LratCheckO8k.lean').write_text(s,encoding='utf-8',newline='\n')
s=v.variant(fast.read_text(),14,8192,'LratO8k','LratFastO8k14','LratCheckO8k')
s+='\n#print axioms Snake9.LratFastO8k14.cp_true\n#print axioms Snake9.LratFastO8k14.final_false\n'
(OUT/'lean/LratFastO8k14.lean').write_text(s,encoding='utf-8',newline='\n')
g.set_width(14,True,4000)
g.OFF=8192;g.BASE_NS='Snake9.LratO8k';g.CHECKER_IMPORT='import LratFastO8k14';g.CHECKER_OPEN='open Snake9.LratFastO8k14\nopen Snake9.LratO8k (Tree TreeTrue andB)'
g.DATA_DEF='noncomputable def'
report=g.export('share120',str(OUT/'certificates'),30000,4,6,True,str(OUT/'lean'),str(OUT/'data'))
f=OUT/'lean/LocalWindowUnsat/ShareWindow120.lean';s=f.read_text();s+='\n#print axioms Snake9.LocalWindow.ShareWindow120.unsat\n';f.write_text(s,encoding='utf-8',newline='\n')
report['checker_offset']=8192;report['word_bits']=14
report['support_sources']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [base,fast,Path(g.__file__),Path(v.__file__)]}
(OUT/'data/export.json').write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True)
