"""Reuse the checked environment and generate two compressed potential candidates."""
from pathlib import Path
import gzip, hashlib, json, sys
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
OLD = ROOT/'milestones/98-concrete-weight-integration'
sys.path.insert(0, str(ROOT/'work/solver_packages'))
import numpy as np
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
(HERE/'.gitattributes').write_text('* -text\n')
env = read(OLD/'data/environment.json')
env['paths'] = [str(HERE/'build'), *env['paths']]
env['receipts'][str((OLD/'data/environment.json').relative_to(ROOT)).replace('\\','/')] = sha(OLD/'data/environment.json')
for p in (OLD/'data').glob('*-audit.json'):
    r = read(p)
    if r.get('status') != 'PASS_CONCRETE_WEIGHT_MODULE': continue
    n = r['module']
    assert sha(OLD/'lean'/f'{n}.lean') == r['source_sha256']
    assert sha(OLD/'build'/f'{n}.olean') == r['olean_sha256']
    assert sha(OLD/r['log']) == r['log_sha256']
    env['receipts'][p.relative_to(ROOT).as_posix()] = sha(p)
    env['sources'][(OLD/'lean'/f'{n}.lean').relative_to(ROOT).as_posix()] = r['source_sha256']
    env['objects'][(OLD/'build'/f'{n}.olean').relative_to(ROOT).as_posix()] = r['olean_sha256']
env['status'] = 'PINNED_REUSED_MILESTONE98_ENVIRONMENT'
(HERE/'data/environment.json').write_text(json.dumps(env,indent=2)+'\n')
s = (OLD/'scripts/check.py').read_text()
s = s.replace("OLD=HERE.parent/'97-geometric-credit-integration'", "OLD=HERE.parent/'97-geometric-credit-integration'")
s = s.replace('PASS_CONCRETE_WEIGHT_MODULE', 'PASS_DEFINED_POTENTIAL_MODULE')
s = s.replace(" and rows\n", "\n")
s = s.replace('Stated concrete credit or combined weight theorem only. Pending local share and reference-catalogue premises, plus complete graph potential, remain separate.', 'Only the declarations printed in this receipt are checked. A pilot or data module does not certify every defined-graph edge.')
(HERE/'scripts/check.py').write_text(s)

def table(xs):
    if len(xs)==1: return f'(Table.leaf {xs[0]})'
    k=len(xs)//2
    return f'(Table.node {k} {table(xs[:k])} {table(xs[k:])})'

specs=[('Completed', ROOT/'milestones/73-countfree-share-catalogue/data/proved-potential.i64.gz',551),
       ('Conditional',ROOT/'milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18-potential.i64.gz',602)]
results=[]
for label,path,bound in specs:
    raw=gzip.decompress(path.read_bytes())
    vals=np.frombuffer(raw,dtype='<i8')
    assert vals.size==1601856 and vals.min()==0 and vals.max()==bound
    current=vals; levels=[]; names=None
    for depth in range(1,6):
        unique,inverse=np.unique(current.reshape(-1,6),axis=0,return_inverse=True)
        module=f'{label}Values99D{depth}'
        previous='PotentialTree99' if depth==1 else f'{label}Values99D{depth-1}'
        lines=[f'import {previous}', '', 'set_option maxHeartbeats 0',
               'set_option maxRecDepth 100000', '', f'namespace Snake9.Potential99.{label}',
               'open Snake9.Potential99', '']
        for i,row in enumerate(unique):
            children=[f'(.leaf {int(v)})' if depth==1 else f'n{depth-1}_{int(v)}' for v in row]
            lines.append(f'def n{depth}_{i} : Tree := .node {6**(depth-1)} '+ ' '.join(children))
        lines += ['', f'end Snake9.Potential99.{label}', '']
        (HERE/'lean'/f'{module}.lean').write_text('\n'.join(lines))
        levels.append(unique); current=inverse
    assert current.size==206
    # Re-expand every entry from the generated indices, independently of Lean.
    decoded=current
    for level in reversed(levels): decoded=level[decoded].reshape(-1)
    assert np.array_equal(decoded,vals)
    roots=[f'n5_{int(i)}' for i in current]
    lines=[f'import {label}Values99D5','',f'namespace Snake9.Potential99.{label}',
           'open Snake9.Potential99 Snake9.Balanced89','',
           'def roots : Table Tree :=',table(roots),'',
           f'def potential (s : Nat) : Nat := min {bound} (value (lookup roots (s/7776) (.leaf 0)) (s%7776))','',
           f'theorem potential_le (s : Nat) : potential s ≤ {bound} := Nat.min_le_left _ _','',
           '#print axioms potential_le',f'end Snake9.Potential99.{label}','']
    (HERE/'lean'/f'{label}Potential99.lean').write_text('\n'.join(lines))
    results.append(dict(profile=label,bound=bound,entries=int(vals.size),unique_leaves=len(np.unique(vals)),
        nodes_by_depth=[len(l) for l in levels],roots=len(roots),
        input=path.relative_to(ROOT).as_posix(),input_sha256=sha(path),
        uncompressed_sha256=hashlib.sha256(raw).hexdigest(),
        reexpanded_sha256=hashlib.sha256(decoded.astype('<i8').tobytes()).hexdigest(),
        exact_reexpansion=True))
(HERE/'data/compression.json').write_text(json.dumps(dict(status='GENERATED_AND_REEXPANDED_CANDIDATES',profiles=results),indent=2)+'\n')
print(json.dumps(results,indent=2))
