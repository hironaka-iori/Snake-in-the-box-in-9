"""Generate exact context equations from the executable Lean table literals.

Generated sources are candidates until the separate checker records success.
No potential certificate or new snake bound is asserted by this script.
"""
from pathlib import Path
import ast
import hashlib
import json
import re

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PINS = {}

def read(rel):
    p = ROOT / rel
    b = p.read_bytes()
    PINS[rel] = hashlib.sha256(b).hexdigest()
    return b.decode('utf-8-sig')

def literal(source, name):
    m = re.search(r'\bdef ' + re.escape(name) + r'\b[^=]*:=\s*', source)
    assert m, name
    start = m.end() + (source[m.end()] == '#')
    assert source[start] == '['
    depth = 0
    for end in range(start, len(source)):
        depth += (source[end] == '[') - (source[end] == ']')
        if not depth:
            return ast.literal_eval(source[start:end+1].replace('#[', '['))
    raise AssertionError(name)

def canon(word):
    names = {}
    return tuple(names.setdefault(x, len(names)) for x in word)

def enc(xs):
    out = 0
    for x in xs:
        out = 6*out+x-1
    return out

def ll(xs):
    return '[' + ','.join(map(str, xs)) + ']'

def suffix(xs, ys):
    return not xs or len(xs) <= len(ys) and list(xs) == list(ys[-len(xs):])

def emit(name, body):
    p = HERE / 'lean' / (name + '.lean')
    # A successful proof source is immutable. Reruns must be byte-identical.
    if (HERE / 'data' / (name+'-audit.json')).exists():
        assert p.read_text(encoding='utf-8') == body
    else:
        p.write_text(body, encoding='utf-8')

tables = read('milestones/77-direction-state-coverage/lean/DirectionTables.lean')
extensions, shapes = literal(tables, 'extensions'), literal(tables, 'shapes')
prefixes = literal(read('milestones/75-exact-history-bridge/history/lean/ExactHistory.lean'), 'prefixes')
geometry = literal(read('milestones/97-geometric-credit-integration/lean/GeometricData97.lean'), 'geometricCredits')
blocks = literal(read('milestones/92-full-witness-batch/lean/ContextAssignmentData.lean'), 'savedBlockClasses')
roots = literal(read('milestones/92-full-witness-batch/lean/BatchContextData.lean'), 'recordedClassRoots')
assert (len(extensions), len(shapes), len(prefixes), len(blocks), len(roots)) == (505,132,75,791,127)
signatures, rules = {}, {}
for batch in range(11):
    sigs = read(f'milestones/94-history-share-dispatch/lean/ShareCover{batch:02d}.lean')
    for name in re.findall(r'def (signature\d+)\b', sigs):
        signatures[name] = literal(sigs, name)
    rs = read(f'milestones/95-history-credit-integration/lean/ConcreteRules95Batch{batch:02d}.lean')
    for name, sig, caps, geo, strong in re.findall(
        r'def (rule\d+) : Rule :=\s*⟨(signature\d+), variants\d+, (\[[^\n]*\]), (\d+), (\d+)⟩', rs):
        rules[name] = dict(sig=signatures[sig], caps=ast.literal_eval(caps), geometric=int(geo), strong=int(strong))
source = read('milestones/95-history-credit-integration/lean/ConcreteRules95.lean')
ordered = [x.strip() for x in re.search(r'def concreteRules : List Rule :=\s*\[([^]]*)\]', source).group(1).split(',')]
assert len(ordered) == len(rules) == 55 and set(ordered) == set(rules)
source = read('milestones/98-concrete-weight-integration/lean/CountConditionedCredits98.lean')
body = source.split('def conditionedCredit',1)[1].split('theorem',1)[0]
conditioned = [(tuple(ast.literal_eval(w)), tuple(ast.literal_eval(s)), int(k)+1)
    for w,s,k in re.findall(r'ruleCredit (\[[^]]+\]) (\[[^]]+\]) (\d+) di code', body)]
assert len(conditioned) == 5
source = read('milestones/98-concrete-weight-integration/lean/CountFreeCredits98.lean')
floors = {}
for name in ['completed', 'conditional']:
    body = source.split(f'def {name}Floor',1)[1].split('def ',1)[0]
    floors[name] = {tuple(ast.literal_eval(w)):int(v) for w,v in re.findall(r'if cs = (\[[^]]+\]) then (\d+)', body)}
floors['conditional'] = floors['completed'] | floors['conditional']

direction_records = []
for di, word in enumerate(extensions):
    forward, backward = canon(word[3:]), canon(word[3:][::-1])
    terms = []
    for cs, syms, amount in conditioned:
        tests = []
        if forward == cs:
            tests.append(f'code%7776 = {enc(syms)}')
        if backward == cs:
            tests.append(f'code%7776 = {enc(syms[::-1])}')
        if tests:
            terms.append('(if ' + ' ∨ '.join(tests) + f' then {amount} else 0)')
    expr = terms[-1] if terms else '0'
    for term in terms[-2::-1]:
        expr = f'max {term} ({expr})'
    direction_records.append(dict(direction=di, forward=list(forward), backward=list(backward),
        geometric=geometry[di], completed=floors['completed'].get(min(forward,backward),0),
        conditional=floors['conditional'].get(min(forward,backward),0), conditioned=expr))

header = '''set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98
'''

def direction_source(ds):
    out = ['import ContextWeights101\nimport StateWalk\nimport DefinedProofGraph\n\n', header]
    for d in ds:
        di = d['direction']
        out.append(f'''
theorem direction_{di} :
    {d['geometric']} = geometricCredits.getD {di} 0 ∧
    {d['completed']} = completedCredit {di} ∧
    {d['conditional']} = conditionalCredit {di} := by decide +kernel

theorem conditioned_{di} (code : Nat) :
    conditionedCredit {di} code = {d['conditioned']} := by
  have hf : canon ((extensions.getD {di} []).drop 3) = {ll(d['forward'])} := by decide +kernel
  have hb : canon (((extensions.getD {di} []).drop 3).reverse) = {ll(d['backward'])} := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_{di}
#print axioms conditioned_{di}
''')
    return ''.join(out)+'\nend Snake9.Context101\n'

# One representative of each distinct conditioned expression is checked first.
pilot = []
seen = set()
for d in direction_records:
    if d['conditioned'] not in seen:
        pilot.append(d)
        seen.add(d['conditioned'])
emit('DirectionPilot101', direction_source(pilot))
pilot_ids = {d['direction'] for d in pilot}
direction_modules = []
emit('Direction101Batch02', direction_source(direction_records[32:48]))
reused_directions = pilot_ids | set(range(32,48))
for start in range(0,505,64):
    name = f'Direction101Group{start//64:02d}'
    ds = direction_records[start:start+64]
    reuse = 'import DirectionPilot101\nimport Direction101Batch02\n' if start == 0 else ''
    emit(name, reuse + direction_source([d for d in ds if d['direction'] not in reused_directions]))
    direction_modules.append(name)

context_records = []
for block, cls in blocks:
    di, q = divmod(block,75)
    word = prefixes[q]+[di]
    selected = [name for name in ordered if suffix(rules[name]['sig'], word)]
    nextq = max(range(75), key=lambda k: len(prefixes[k]) if suffix(prefixes[k],word) else -1)
    src_shape = shapes.index(list(canon(extensions[di][:-1])))
    dst_shape = shapes.index(list(canon(extensions[di][1:])))
    src = src_shape*7776 if q == 0 else 1026432+(q-1)*7776
    dst = dst_shape*7776 if nextq == 0 else 1026432+(nextq-1)*7776
    context_records.append(dict(direction=di,history=q,block=block,cls=cls,root=roots[cls],
        source_base=src,target_base=dst,selected=selected,**{k:v for k,v in direction_records[di].items() if k!='direction'}))

def context_source(cs, pilot_import=False, explicit_imports=None):
    modules = explicit_imports or (['DirectionPilot101'] if pilot_import else sorted({f"Direction101Group{c['direction']//64:02d}" for c in cs}))
    out = [''.join(f'import {name}\n' for name in modules)+'\n',header]
    for c in cs:
        di,q = c['direction'],c['history']
        tag = f'{di}_{q}'
        selected = ll(c['selected'])
        out.append(f'''
theorem selected_{tag} :
    {selected} = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD {q} [] ++ [{di}])) := by rfl

theorem source_{tag} (code : Nat) :
    edgeSource {q} {di} code = {c['source_base']}+code/6 := by rfl

theorem target_{tag} (code : Nat) :
    edgeTarget {q} {di} code = {c['target_base']}+code%7776 := by rfl

theorem block_{tag} :
    savedBlockClass (75*{di}+{q}) = some {c['cls']} ∧
    recordedClassRoot {c['cls']} = {c['root']} := by decide +kernel
''')
        for profile,field in [('completed','2.1'),('conditional','2.2')]:
            out.append(f'''
theorem {profile}_{tag} (code : Nat) :
    weight {profile}Credit {q} {di} code =
      120*(code%6+1)+max (max {c['geometric']} (emittedCredit {selected} code))
        (max ({c['conditioned']}) {c[profile]}) :=
  weight_eq_context {profile}Credit {q} {di} {selected} {c['geometric']} {c[profile]}
    (fun code => {c['conditioned']}) selected_{tag} direction_{di}.1
    direction_{di}.{field} conditioned_{di} code
''')
        for prefix in ['selected','source','target','block','completed','conditional']:
            out.append(f'#print axioms {prefix}_{tag}\n')
    return ''.join(out)+'\nend Snake9.Context101\n'

# Pilot includes empty and emitting histories, with at most eight contexts.
cpilot = [c for c in context_records if c['direction'] in pilot_ids and c['history']==0]
emitting = next(c for c in context_records if c['selected'])
pilot_blocks = {c['block'] for c in cpilot}
context_modules = []
for start in range(0,791,64):
    name = f'Context101Group{start//64:02d}'
    cs = context_records[start:start+64]
    reuse = ('import ContextPilot101\n' if any(c['block'] in pilot_blocks for c in cs) else '')
    reuse += ('import EmittingPilot101\n' if any(c['block']==emitting['block'] for c in cs) else '')
    emit(name, reuse+context_source([c for c in cs if c['block'] not in pilot_blocks and c['block']!=emitting['block']]))
    context_modules.append(name)
emit('ContextPilot101', context_source(cpilot,True))
emit('EmittingPilot101', context_source([emitting],explicit_imports=['Direction101Batch02']))
emit('AllContextSpecializations101', ''.join(f'import {name}\n' for name in context_modules)+
    '\n-- Import check for every generated context, including the reused pilot modules.\n'+
    '#check Snake9.Context101.completed_0_0\n#check Snake9.Context101.conditional_504_0\n')
data = dict(status='GENERATED_NOT_YET_LEAN_CHECKED',inputs_sha256=PINS,
    directions=direction_records,contexts=context_records,pilot_directions=sorted(pilot_ids),
    emitting_pilot=[emitting['direction'],emitting['history']],
    direction_modules=direction_modules,context_modules=context_modules)
(HERE/'data/generated-contexts.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print('GENERATED',len(direction_records),'directions,',len(context_records),'contexts; pilot',sorted(pilot_ids),'; emitting',data['emitting_pilot'])
