"""Split exhaustive coverage at six directions; Lean checks every branch."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
model=json.loads((HERE/'data/tables.json').read_text())
prefixes=sorted({tuple(row[:6]) for row in model['extensions']})
def induced(xs):
    for i in range(len(xs)):
        parity=set()
        for j in range(i,len(xs)):
            parity.symmetric_difference_update([xs[j]])
            if not parity or (j>i and len(parity)==1):return False
    return True
fmt=lambda xs:str(list(xs))
names=[]
for ix,pre in enumerate(prefixes):
    name=f'CoverageLeaf{ix:02d}';names.append(name)
    if ix==11:
        assert pre==(0,1,2,3,4,5)
        for a in range(7):
            child=pre+(a,);tailname=f'CoverageTail{a:02d}'
            childlines=['import DirectionTables','import PrunedEnumeration',
                'namespace Snake9.Direction77','open Snake9.WindowAutomaton',
                'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
            for length,table in [(8,'shapes'),(9,'extensions')]:
                childlines += [f'theorem tail_{length}_{a} : allPruned {length-7} {max(child)+1} {fmt(child)}',
                    f'    (fun c => {table}.contains c) = true := by decide +kernel',
                    f'#print axioms tail_{length}_{a}']
            childlines.append('end Snake9.Direction77')
            (HERE/'lean'/f'{tailname}.lean').write_text('\n'.join(childlines)+'\n',encoding='utf-8')
        lines=['import PrunedAssembly']+[f'import CoverageTail{a:02d}' for a in range(7)]+[
            'namespace Snake9.Direction77','open Snake9.WindowAutomaton']
        for length,table in [(8,'shapes'),(9,'extensions')]:
            lines += [f'theorem leaf_{length}_{ix} : allPruned {length-6} 6 {fmt(pre)}',
                f'    (fun c => {table}.contains c) = true := by',
                '  apply allPruned_step','  intro a ha','  interval_cases a']+[
                f'  · exact tail_{length}_{a}' for a in range(7)]+[f'#print axioms leaf_{length}_{ix}']
        lines.append('end Snake9.Direction77')
        (HERE/'lean'/f'{name}.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
        continue
    lines=['import DirectionTables','import PrunedEnumeration',
           'namespace Snake9.Direction77','open Snake9.WindowAutomaton',
           'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    for length,table in [(8,'shapes'),(9,'extensions')]:
        theorem=f'leaf_{length}_{ix}'
        lines += [f'theorem {theorem} : allPruned {length-6} {max(pre)+1} {fmt(pre)}',
                  f'    (fun c => {table}.contains c) = true := by decide +kernel',
                  f'#print axioms {theorem}']
    lines += ['end Snake9.Direction77']
    (HERE/'lean'/f'{name}.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
lines=['import PrunedAssembly']+[f'import {name}' for name in names]+[
    'namespace Snake9.Direction77','open Snake9.WindowAutomaton',
    'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
for length,table in [(8,'shapes'),(9,'extensions')]:
    def visit(pre):
        suffix='root' if not pre else ''.join(map(str,pre))
        theorem=f'coverage_{length}_{suffix}'
        bound=max(pre,default=-1)+1
        if len(pre)==6 and induced(pre):
            assert pre in prefixes
            return f'leaf_{length}_{prefixes.index(pre)}'
        if induced(pre):
            children=[]
            for a in range(bound+1):children.append(visit(pre+(a,)))
            proof=['  apply allPruned_step','  intro a ha','  interval_cases a']+[
                f'  · exact {child}' for child in children]
        else:proof=['  decide +kernel']
        lines.extend([f'theorem {theorem} : allPruned {length-len(pre)} {bound} {fmt(pre)}',
                      f'    (fun c => {table}.contains c) = true := by']+proof)
        return theorem
    visit(())
    lines.append(f'#print axioms coverage_{length}_root')
lines.append('end Snake9.Direction77')
(HERE/'lean/CoverageAssembly.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
(HERE/'data/coverage-chunks.json').write_text(json.dumps(dict(prefixes=prefixes,modules=names,
    extra_tail_modules=[f'CoverageTail{i:02d}' for i in range(7)],
    scope='Each leaf and every rejected branch must pass Lean; Python pruning is not trusted.'),indent=2)+'\n')
print(len(prefixes),'leaf modules generated')
