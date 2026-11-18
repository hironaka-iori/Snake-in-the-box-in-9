"""Preserve the 623 literal claims in small synchronous Lean modules."""
from pathlib import Path
import hashlib, json, re
H = Path(__file__).resolve().parents[1]
claims = {}
pins = {}
for p in sorted((H/'majority/certificates').glob('Cuts*.lean')):
    text = p.read_text(encoding='utf-8')
    pins[str(p)] = hashlib.sha256(p.read_bytes()).hexdigest()
    for name, body in re.findall(r'(theorem (cut237_\d+) :.*?:= by decide \+kernel)', text, re.S):
        index = int(body.split('_')[-1])
        assert index not in claims
        claims[index] = name
assert set(claims) == set(range(623))
header = 'import CubeCut\nopen CubeCut237\nset_option Elab.async false\nset_option autoImplicit false\nset_option maxRecDepth 10000\nset_option maxHeartbeats 10000000\n\n'
groups = []
for start in range(0, 623, 5):
    ids = list(range(start, min(start+5, 623)))
    text = header + '\n\n'.join(claims[i] for i in ids) + '\n\n'
    text += '\n'.join(f'#print axioms cut237_{i:03}' for i in ids) + '\n'
    name = f'CutBatch{start:03}'
    p = H/'lean'/(name+'.lean')
    assert not p.exists()
    p.write_text(text, encoding='utf-8', newline='\n')
    groups.append(dict(module=name, indices=ids, source_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(H/'data/cut-batches.json').write_text(json.dumps(dict(statements=623, original_pins=pins, groups=groups), indent=2)+'\n', encoding='utf-8')
print('GENERATED_EXACT_CUT_BATCHES', len(groups), 'statements', sum(len(g['indices']) for g in groups))
