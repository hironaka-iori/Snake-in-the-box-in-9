"""Generate joint-traversal checks and identical-weight prefix comparisons."""
from pathlib import Path
import argparse, hashlib, json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
parser = argparse.ArgumentParser()
parser.add_argument('--contexts', nargs='+', default=['99:37', '0:0'])
parser.add_argument('--baseline', action='store_true')
parser.add_argument('--method', choices=['joint', 'baseline'], default='joint')
parser.add_argument('--all', action='store_true')
args = parser.parse_args()
cp = ROOT/'milestones/101-context-specialization/data/generated-contexts.json'
bp = ROOT/'milestones/102-potential-block-reduction/data/candidates.json'
data = read(cp)
blocks = read(bp)['blocks']
inputs = {p.relative_to(ROOT).as_posix(): sha(p) for p in [cp, bp]}
requested = {tuple(map(int, x.split(':'))) for x in args.contexts}

def save(name, source):
    path = HERE/'lean'/(name+'.lean')
    if path.exists() and path.read_text(encoding='utf-8') == source:
        return
    assert not (HERE/'data/check.lock').exists(), 'Do not edit sources during a check.'
    assert not (HERE/'data'/(name+'-audit.json')).exists(), name
    path.write_text(source, encoding='utf-8')

specs = []
for index, c in enumerate(data['contexts']):
    di, q = c['direction'], c['history']
    if not args.all and (di, q) not in requested:
        continue
    sb, tb = c['source_base']//7776, c['target_base']//7776
    assert c['source_base'] == 7776*sb and c['target_base'] == 7776*tb
    for profile, P, R in [('completed', 483, 551), ('conditional', 496, 602)]:
        title, tag = profile.title(), f'{di}_{q}'
        sroot, troot = blocks[profile][sb], blocks[profile][tb]
        imports = ['JointTraversal103', 'BoundedPrefixTransfer102', f'Context101Group{index//64:02d}']
        imports += sorted({f'PotentialRoots102Group{sb//52:02d}', f'PotentialRoots102Group{tb//52:02d}'})
        selected = '['+','.join(c['selected'])+']'
        weight = f"120*(code%6+1)+max (max {c['geometric']} (emittedCredit {selected} code)) (max ({c['conditioned']}) {c[profile]})"
        weight_lemma = f'{profile}_{tag}'
        if (di, q) == (99, 37):
            imports += ['EmittingReduction101']
            weight = '120*(code%6+1)+max (if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18) (if code%7776 = 3221 then 96 else 0)'
            weight_lemma = f'{profile}_simplified_{tag}'
        test = f'''(fun code => decide
      ({P}+min {R} (value {title}.{troot} (code%7776)) ≤
        {weight}+min {R} (value {title}.{sroot} (code/6))))'''
        for method in (['joint', 'baseline'] if args.baseline else [args.method]):
            name = f'{title}{method.title()}103D{di}Q{q}'
            namespace = 'JointCertificates103' if method == 'joint' else 'Baseline103'
            text = ''.join(f'import {x}\n' for x in imports)+f'''
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.{namespace}
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79
'''
            if method == 'joint':
                text += f'''
theorem {profile}_joint_{tag} :
    checkJoint (fun code => {weight}) {P} {R} 6 0 {c['root']}
      {title}.{sroot} {title}.{troot} = true := by decide +kernel

theorem {profile}_prefix_{tag} :
    checkPrefix {test} 6 0 {c['root']} = true := by
  exact joint_root_prefix _ {P} {R} {c['root']} {title}.{sroot} {title}.{troot}
    {profile}_joint_{tag}
'''
            else:
                text += f'''
theorem {profile}_prefix_{tag} :
    checkPrefix {test} 6 0 {c['root']} = true := by decide +kernel
'''
            text += f'''
theorem {profile}_context_{tag} :
    contextCheck (weight {profile}Credit) {P} {title}.potential {di} {q} = true := by
  apply contextCheck_of_bounded_prefix {test}
    (weight {profile}Credit) {P} {title}.potential {di} {q} {c['cls']} block_{tag}.1
  · simpa only [block_{tag}.2] using {profile}_prefix_{tag}
  · intro code hc _
    have hs := {profile}_at_{sb} (code/6) (by omega)
    have ht := {profile}_at_{tb} (code%7776) (by omega)
    simp only [{weight_lemma}, source_{tag}, target_{tag}, hs, ht]

'''
            if method == 'joint':
                text += f'#print axioms {profile}_joint_{tag}\n'
            text += f'''#print axioms {profile}_prefix_{tag}
#print axioms {profile}_context_{tag}
end Snake9.{namespace}
'''
            save(name, text)
            specs.append(dict(module=name, profile=profile, method=method, direction=di,
                history=q, slope=P, range=R, cls=c['cls'], root=c['root'],
                source_block=sb, target_block=tb, source_node=sroot, target_node=troot))
assert args.all or requested == {(x['direction'], x['history']) for x in specs}
path = HERE/'data/candidates.json'
previous = read(path) if path.exists() else dict(inputs_sha256=inputs, specs=[])
assert previous['inputs_sha256'] == inputs
merged = {x['module']: x for x in previous['specs']}
for spec in specs:
    assert spec['module'] not in merged or merged[spec['module']] == spec
    merged[spec['module']] = spec
path.write_text(json.dumps(dict(status='GENERATED_CANDIDATES_CHECK_RECEIPTS_FOR_CURRENT_STATUS',
    inputs_sha256=inputs, specs=list(merged.values())), indent=2)+'\n', encoding='utf-8')
print('GENERATED', len(specs), 'candidates;', len(merged), 'total')
