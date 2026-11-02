"""Split finite round-trip/map checks into six consecutive index blocks."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1]
modules=[]
for ix,lo in enumerate(range(0,505,100)):
    n=min(100,505-lo);name=f'LookupChunk{ix:02d}';modules.append(name)
    lines=['import LookupDefinitions','namespace Snake9.Direction77',
        'open Snake9.WindowAutomaton','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    if ix==0:lines += ['theorem shape_roundtrip : allBelow 132 (lookupCheck shapes) = true := by decide +kernel',
        '#print axioms shape_roundtrip']
    for kind,p in [('direction','lookupCheck extensions'),('maps','mapCheck')]:
        lines += [f'theorem {kind}_chunk_{ix} : allBelow {n} (fun i => ({p}) ({lo}+i)) = true := by decide +kernel',
            f'#print axioms {kind}_chunk_{ix}']
    lines.append('end Snake9.Direction77')
    (HERE/'lean'/f'{name}.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
lines=[f'import {name}' for name in modules]+['namespace Snake9.Direction77','open Snake9.WindowAutomaton']
for kind,p in [('direction','lookupCheck extensions'),('maps','mapCheck')]:
    lines += [f'theorem {kind}_partial_0 : allBelow 0 ({p}) = true := rfl']
    for ix,lo in enumerate(range(0,505,100)):
        n=min(100,505-lo);hi=lo+n
        lines += [f'theorem {kind}_partial_{hi} : allBelow {hi} ({p}) = true := by',
            f'  calc allBelow {hi} ({p}) = (allBelow {lo} ({p}) &&',
            f'      allBelow {n} (fun i => ({p}) ({lo}+i))) := allBelow_add {lo} {n} _',
            f'    _ = true := by rw [{kind}_partial_{lo}, {kind}_chunk_{ix}]; rfl']
lines += ['theorem shape_lookup_checked : allBelow 132 (lookupCheck shapes) = true := shape_roundtrip',
    'theorem direction_lookup_checked : allBelow 505 (lookupCheck extensions) = true := direction_partial_505',
    'theorem map_checked : allBelow 505 mapCheck = true := maps_partial_505']
old=(HERE/'diagnostics/LookupTableCheck.monolithic.lean').read_text()
tail=old[old.index('theorem shape_index_getD'):]
(HERE/'lean/LookupTableCheck.lean').write_text('\n'.join(lines)+'\n\n'+tail,encoding='utf-8')
print('Six lookup chunks generated')
