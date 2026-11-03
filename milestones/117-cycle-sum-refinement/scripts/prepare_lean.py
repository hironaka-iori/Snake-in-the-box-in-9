"""State the new geometric implication with its pending contradiction explicit."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
(HERE/'lean').mkdir(exist_ok=True)
source=ROOT/'milestones/112-critical-sum-refinement/lean/SumGeometry112.lean'
text=source.read_text(encoding='utf-8')
for old,new in [
 ('SumGeometry112','SumGeometry117'),
 ('[0,1,2,3,1,4]','[0,1,2,0,3,4]'),
 ('[(0,21),(0,21),(0,2),(0,21),(0,21)]','[(0,21),(0,21),(0,5),(0,21),(0,21)]'),
 ('absentCorners S 15 3 1 + absentCorners S 13 1 4 ≤ 18','absentCorners S 6 0 3 + absentCorners S 14 3 4 ≤ 15'),
 ('coreAlpha p (r+3) ≤ 2','coreAlpha p (r+3) ≤ 5'),
 ('19 ≤ coreAlpha','16 ≤ coreAlpha'),
 ('[0,1,3,7,15,13,29]','[0,1,3,7,6,14,30]'),
 ('dirOfStep 7 15 = 3','dirOfStep 7 6 = 0'),
 ('dirOfStep 15 13 = 1','dirOfStep 6 14 = 3'),
 ('dirOfStep 13 29 = 4','dirOfStep 14 30 = 4')]:
    assert old in text,old;text=text.replace(old,new)
marker='#print axioms actual_outer_sum'
assert marker in text
extra='''theorem comparison_barrier (p d R : Nat) (h : 6*p ≤ 2915*d) :
    (4200*d+p)*235 ≤ 1098960*d+8*p+R := by
  omega

theorem comparison_value :
    ((1098960*6+8*2915+3460 : Rat)/(4200*6+2915)) = (1324108 : Rat)/5623 := by
  norm_num

#print axioms comparison_barrier
#print axioms comparison_value

'''
text=text.replace(marker,extra+marker)
target=HERE/'lean/SumGeometry117.lean';assert not target.exists();target.write_text(text,encoding='utf-8')
checker=ROOT/'milestones/114-total-count-pressure/scripts/check_total_geometry.py'
code=checker.read_text(encoding='utf-8').replace('TotalGeometry114','SumGeometry117').replace('build-total-geometry','build-geometry')
code=code.replace("==1\n", "==3\n").replace("== 1\n", "== 3\n")
code=code.replace("==source.read_text(encoding='utf-8').count('#print axioms')==1", "==source.read_text(encoding='utf-8').count('#print axioms')==3")
code=code.replace("assert len(rows)==source.read_text(encoding='utf-8').count('#print axioms')==1", "assert len(rows)==source.read_text(encoding='utf-8').count('#print axioms')==3")
code=code.replace('Actual-snake canonical012310 total-count transfer under an explicit local contradiction; no concrete local refutation is imported.', 'Actual-snake 012034 outer-sum transfer under an explicit local contradiction, and exact comparison arithmetic; concrete local refutation remains pending.')
code=code.replace("PASS_TOTAL_GEOMETRY","PASS_CONDITIONAL_SUM_GEOMETRY_AND_COMPARISON")
target=HERE/'scripts/check_geometry.py';assert not target.exists();target.write_text(code,encoding='utf-8')
(HERE/'data/lean-source-pins.json').write_text(json.dumps({p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in [source,checker]},indent=2)+'\n',encoding='utf-8')
print('Prepared geometric transfer with explicit local contradiction and two arithmetic deductions.')
