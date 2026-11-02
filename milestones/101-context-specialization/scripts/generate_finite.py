"""Select a genuinely count-dependent history context for both finite checks."""
from pathlib import Path
import ast
import gzip
import hashlib
import json
import re
import struct

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
data = read(HERE/'data/generated-contexts.json')
rules = {}
pins = {'generated-contexts.json':sha(HERE/'data/generated-contexts.json')}
for p in sorted((ROOT/'milestones/95-history-credit-integration/lean').glob('ConcreteRules95Batch*.lean')):
    pins[p.relative_to(ROOT).as_posix()] = sha(p)
    for name,caps,geo,strong in re.findall(r'def (rule\d+) : Rule :=\s*⟨signature\d+, variants\d+, (\[[^\n]*\]), (\d+), (\d+)⟩',p.read_text()):
        rules[name] = dict(caps=ast.literal_eval(caps),geometric=int(geo),strong=int(strong))
dp = ROOT/'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz'
ap = ROOT/'milestones/100-prefix-potential-checker/data/prefix-enumeration-audit.json'
dag = json.loads(gzip.decompress(dp.read_bytes()))
prior = read(ap)
pins[dp.relative_to(ROOT).as_posix()] = sha(dp)
pins[ap.relative_to(ROOT).as_posix()] = sha(ap)
conditioned_source = ROOT/'milestones/98-concrete-weight-integration/lean/CountConditionedCredits98.lean'
pins[conditioned_source.relative_to(ROOT).as_posix()] = sha(conditioned_source)
body = conditioned_source.read_text().split('def conditionedCredit',1)[1].split('theorem',1)[0]
conditioned_rules = [(ast.literal_eval(w), ast.literal_eval(s), int(k)+1)
    for w,s,k in re.findall(r'ruleCredit (\[[^]]+\]) (\[[^]]+\]) (\d+) di code',body)]
def encode(xs):
    out = 0
    for x in xs:
        out = 6*out+x-1
    return out
def conditioned(c,code):
    return max([0]+[amount for word,syms,amount in conditioned_rules
        if (c['forward']==word and code%7776==encode(syms))
        or (c['backward']==word and code%7776==encode(syms[::-1]))])
def accepted(root):
    found = []
    def visit(depth,prefix,node):
        if node == 0:
            return
        if depth == 0:
            assert node == 1
            found.append(prefix)
            return
        for j in range(6):
            visit(depth-1,6*prefix+j,node if node<2 else dag['nodes'][node-2][j+1])
    visit(6,0,root)
    return found
for index,c in enumerate(data['contexts']):
    if len(c['selected']) != 1:
        continue
    rule = rules[c['selected'][0]]
    if not rule['caps'] or rule['strong'] <= max(rule['geometric'],c['geometric'],c['conditional']):
        continue
    codes = accepted(c['root'])
    digest = hashlib.sha256(b''.join(struct.pack('<q',x) for x in codes)).hexdigest()
    old = prior['classes'][c['cls']]
    assert len(codes)==old['accepted_codes'] and digest==old['codes_i64_sha256']
    raised,uncapped = [],[]
    for code in codes:
        digits = [code//6**(5-j)%6+1 for j in range(6)]
        capped = all(digits[j]<=bound for j,bound in rule['caps'])
        base = max(c['geometric'],c['conditional'],conditioned(c,code),rule['geometric'])
        if capped and rule['strong']>base:
            raised.append(dict(code=code,digits=digits,credit_without_strong=base,credit_with_strong=rule['strong']))
        if not capped:
            uncapped.append(dict(code=code,digits=digits))
    if raised and uncapped:
        break
else:
    raise AssertionError('No accepted context tests a history-driven weight increase')
selection = dict(accepted_edges=len(codes),codes_i64_sha256=digest,
    accepted_codes_raised_in_both_profiles=len(raised),raised_example=raised[0],
    caps_false_example=uncapped[0],rule=rule,
    scope='Numerical selection check; the generated potential statements still require Lean.')
di,q = c['direction'],c['history']
assert (di,q)==(99,37), 'The separately proved reduction is specific to this context'
tag = f'{di}_{q}'
selected = '['+','.join(c['selected'])+']'
specs = []
for profile,P in [('completed',483),('conditional',496)]:
    title = profile.title()
    name = f'{title}Emitting101'
    expr = '120*(code%6+1)+max (if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18) (if code%7776 = 3221 then 96 else 0)'
    source = f'''import PrefixChecker100
import EmittingReduction101
import {title}Potential99

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.PrefixCertificates101
open Snake9.PrefixChecker100 Snake9.PotentialChecker99 Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.Context101 Snake9.ConcreteCatalogue95
open Snake9.Guards79

theorem {profile}_prefix_{tag} :
    checkPrefix (fun code => decide
      ({P}+{title}.potential ({c['target_base']}+code%7776) ≤
        {expr}+{title}.potential ({c['source_base']}+code/6)))
      6 0 {c['root']} = true := by decide +kernel

theorem {profile}_context_{tag} :
    contextCheck (weight {profile}Credit) {P} {title}.potential {di} {q} = true := by
  apply contextCheck_of_prefix (weight {profile}Credit) {P} {title}.potential {di} {q} {c['cls']}
  · exact block_{tag}.1
  · rw [block_{tag}.2]
    simpa only [{profile}_simplified_{tag}, source_{tag}, target_{tag}]
      using {profile}_prefix_{tag}

#print axioms {profile}_prefix_{tag}
#print axioms {profile}_context_{tag}
end Snake9.PrefixCertificates101
'''
    path = HERE/'lean'/(name+'.lean')
    if (HERE/'data'/(name+'-audit.json')).exists():
        assert path.read_text(encoding='utf-8') == source
    else:
        path.write_text(source,encoding='utf-8')
    specs.append(dict(module=name,profile=profile,slope=P,**c,rule=rules[c['selected'][0]]))
(HERE/'data/finite-contexts.json').write_text(json.dumps(dict(status='GENERATED_NOT_YET_CHECKED',inputs_sha256=pins,selection=selection,specs=specs),indent=2)+'\n')
print('FINITE CANDIDATES',di,q,c['selected'],rules[c['selected'][0]],'class',c['cls'])
