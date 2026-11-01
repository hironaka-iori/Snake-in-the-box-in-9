"""Choose exact encoding widths, generate sound checkers and simulate the export."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1];OUT=HERE/'cases'/f'case{int(sys.argv[1])}'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
case=read(OUT/'data/case.json');slug=case['slug'];meta=read(OUT/f'data/{slug}.json');gen=read(OUT/'data/lrat-generation.json')
assert gen['status']=='COMPACT_LRAT_GENERATED'
assert sha(OUT/f'certificates/{slug}.cnf')==gen['cnf_sha256'] and sha(OUT/f'certificates/{slug}.lrat')==gen['lrat_sha256']
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
import gen_checker_variants as v
import gen_lean_lrat as g
clauses=g.read_cnf_core(str(OUT/f'certificates/{slug}.cnf'),meta['core_ids'])
lemmas=g.read_lrat(str(OUT/f'certificates/{slug}.lrat'))
_,_,_,slots=g.plan(meta['core_ids'],lemmas)
off=1<<meta['active_variables'].bit_length();bits=max(13,slots.bit_length(),(off+meta['active_variables']+1).bit_length())
assert bits<=15,(slots,off,bits)
base_name=f'LratOffset{off}';base_module=f'LratCheckOffset{off}';fast_name=f'LratFastOffset{off}W{bits}'
base=ROOT/'work/final_lean/LratCheck.lean';fast=ROOT/'work/final_lean/LratFast.lean'
s=v.variant(base.read_text(),13,off,base_name,'LratFast','LocalWindowModel')
s+=f'\n#print axioms Snake9.{base_name}.rawMask_true\n#print axioms Snake9.{base_name}.start_true\n'
(OUT/f'lean/{base_module}.lean').write_text(s,encoding='utf-8',newline='\n')
s=v.variant(fast.read_text(),bits,off,base_name,fast_name,base_module)
s+=f'\n#print axioms Snake9.{fast_name}.cp_true\n#print axioms Snake9.{fast_name}.final_false\n'
(OUT/f'lean/{fast_name}.lean').write_text(s,encoding='utf-8',newline='\n')
g.set_width(bits,True,4000);g.OFF=off;g.BASE_NS=f'Snake9.{base_name}'
g.CHECKER_IMPORT=f'import {fast_name}';g.CHECKER_OPEN=f'open Snake9.{fast_name}\nopen Snake9.{base_name} (Tree TreeTrue andB)';g.DATA_DEF='noncomputable def'
report=g.export(slug,str(OUT/'certificates'),30000,4,6,True,str(OUT/'lean'),str(OUT/'data'))
f=OUT/f"lean/LocalWindowUnsat/{case['namespace']}.lean";s=f.read_text();s+=f"\n#print axioms Snake9.LocalWindow.{case['namespace']}.unsat\n";f.write_text(s,encoding='utf-8',newline='\n')
report.update(checker_offset=off,word_bits=bits,support_sources={str(p.relative_to(ROOT)):sha(p) for p in [base,fast,Path(g.__file__),Path(v.__file__)]})
(OUT/'data/export.json').write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True)
