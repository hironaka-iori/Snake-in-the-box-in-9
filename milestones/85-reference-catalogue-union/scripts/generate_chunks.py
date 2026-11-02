"""Generate small exact selection witnesses for all 1,378 reference keys."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
rows=json.loads((HERE/'data/reference-union.json').read_text())['rows'];assert len(rows)==1378
fmt=lambda xs:'['+','.join(map(str,xs))+']'
key=lambda r:'('+fmt(r['directions'])+','+fmt(r['symbols'])+')'
names=[]
for start in range(0,len(rows),64):
    i=start//64;part=rows[start:start+64];name=f'ReferenceChunk{i:02d}';names.append(name)
    src=['import ReferencePicks','','namespace Snake9.Reference85','set_option maxRecDepth 100000',
      'set_option maxHeartbeats 2000000','',f'def picks{i:02d} : List Pick := [',
      ',\n'.join('('+('false' if r['source_catalogue']==235 else 'true')+','+str(r['source_index'])+')' for r in part),']','',
      f'def keys{i:02d} : List Key := [',',\n'.join(key(r) for r in part),']','',
      f'theorem picks{i:02d}_valid : picks{i:02d}.all pickValid = true := by decide +kernel',
      f'theorem keys{i:02d}_exact : keys{i:02d} = picks{i:02d}.map pickKey := by decide +kernel',
      f'theorem keys{i:02d}_valid : keys{i:02d}.all keyValid = true := by decide +kernel',
      f'theorem keys{i:02d}_covered : keys{i:02d}.all keyCovered = true := by',
      f'  rw [keys{i:02d}_exact]',f'  exact picks_covered picks{i:02d} picks{i:02d}_valid','',
      f'#print axioms picks{i:02d}_valid',f'#print axioms keys{i:02d}_exact',
      f'#print axioms keys{i:02d}_valid',f'#print axioms keys{i:02d}_covered','end Snake9.Reference85','']
    (HERE/'lean'/(name+'.lean')).write_text('\n'.join(src))
src=['import '+n for n in names]+['','namespace Snake9.Reference85','open Snake9.LocalWindow',
    'set_option maxRecDepth 100000','set_option maxHeartbeats 2000000','',
    'def referenceKeys : List Key := '+' ++ '.join(f'keys{i:02d}' for i in range(len(names))),'',
    'theorem referenceKeys_valid : referenceKeys.all keyValid = true := by',
    '  simp only [referenceKeys,List.all_append,'+','.join(f'keys{i:02d}_valid' for i in range(len(names)))+',Bool.true_and]','',
    'theorem referenceKeys_covered : referenceKeys.all keyCovered = true := by',
    '  simp only [referenceKeys,List.all_append,'+','.join(f'keys{i:02d}_covered' for i in range(len(names)))+',Bool.true_and]','',
    'theorem referenceKeys_length : referenceKeys.length = 1378 := by decide +kernel','',
    'theorem reference_union_refuted (h235 : AllRefuted6K235) (h236 : AllRefuted236) :',
    '    AllRefutedList referenceKeys := allRefuted_of_covered h235 h236 _ referenceKeys_covered','',
    'theorem concrete_reference_retained (h235 : AllRefuted6K235) (h236 : AllRefuted236)',
    '    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m)',
    '    (k : Key) (hk : k ∈ referenceKeys) (s : Nat) (hs : s+k.2.length ≤ 6) :',
    '    ¬ forwardHit p r s k ∧ ¬ reverseHit p r s k :=',
    '  all_reference_guards_retained h235 h236 referenceKeys referenceKeys_valid referenceKeys_covered p r hr k hk s hs','',
    '#print axioms referenceKeys_valid','#print axioms referenceKeys_covered','#print axioms referenceKeys_length',
    '#print axioms reference_union_refuted','#print axioms concrete_reference_retained','end Snake9.Reference85','']
(HERE/'lean/ReferenceUnion.lean').write_text('\n'.join(src))
(HERE/'data/chunk-plan.json').write_text(json.dumps(dict(chunk_size=64,chunks=names,keys=1378,
    scope='Indexed source witnesses avoid repeated full-list searches; each equality and index bound is checked by Lean.'),indent=2)+'\n')
print('Generated',len(names),'chunks and final union assembly')
