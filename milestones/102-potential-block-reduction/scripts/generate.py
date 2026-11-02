"""Generate fixed-root potential equations and bounded finite-check candidates."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={}
cp=ROOT/'milestones/101-context-specialization/data/generated-contexts.json'
data=read(cp);pins[cp.relative_to(ROOT).as_posix()]=sha(cp)
blocks={}
for profile in ['completed','conditional']:
    p=ROOT/f'milestones/99-defined-potential-certificates/lean/{profile.title()}Potential99.lean'
    pins[p.relative_to(ROOT).as_posix()]=sha(p)
    body=p.read_text().split('def roots',1)[1].split('def potential',1)[0]
    blocks[profile]=re.findall(r'Table\.leaf (n5_\d+)',body)
    assert len(blocks[profile])==206
def save(name,source):
    p=HERE/'lean'/(name+'.lean')
    if p.exists() and p.read_text(encoding='utf-8')==source:return
    if (HERE/'data'/(name+'-audit.json')).exists():assert p.read_text(encoding='utf-8')==source,name
    else:p.write_text(source,encoding='utf-8')
groups=[]
for start in range(0,206,52):
    name=f'PotentialRoots102Group{start//52:02d}';groups.append(name)
    text='''import PotentialBlocks102

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.PotentialBlocks102
open Snake9.Potential99 Snake9.Balanced89
'''
    for i in range(start,min(start+52,206)):
        for profile,R in [('completed',551),('conditional',602)]:
            title=profile.title();node=blocks[profile][i]
            text+=f'''
theorem {profile}_at_{i} (offset : Nat) (hoff : offset < 7776) :
    {title}.potential ({7776*i}+offset) =
      min {R} (value {title}.{node} offset) := by
  have hr : lookup {title}.roots {i} (.leaf 0) = {title}.{node} := by rfl
  simpa only [hr] using {profile}_block {i} offset hoff

#print axioms {profile}_at_{i}
'''
    save(name,text+'\nend Snake9.PotentialBlocks102\n')
targets=[(99,37,'benchmark'),(0,0,'new'),(1,0,'new'),(9,0,'new'),(10,0,'new')]
specs=[]
for di,q,role in targets:
    index,c=next((i,c) for i,c in enumerate(data['contexts']) if (c['direction'],c['history'])==(di,q))
    sb,tb=c['source_base']//7776,c['target_base']//7776
    assert c['source_base']==7776*sb and c['target_base']==7776*tb
    for profile,P,R in [('completed',483,551),('conditional',496,602)]:
        title=profile.title();tag=f'{di}_{q}';name=f'{title}Block102D{di}Q{q}'
        sroot,troot=blocks[profile][sb],blocks[profile][tb]
        imports=['BoundedPrefixTransfer102',f'Context101Group{index//64:02d}']
        imports+=sorted({f'PotentialRoots102Group{sb//52:02d}',f'PotentialRoots102Group{tb//52:02d}'})
        selected='['+','.join(c['selected'])+']'
        weight=f"120*(code%6+1)+max (max {c['geometric']} (emittedCredit {selected} code)) (max ({c['conditioned']}) {c[profile]})"
        weight_lemma=f'{profile}_{tag}'
        if (di,q)==(99,37):
            imports+=['EmittingReduction101']
            weight='120*(code%6+1)+max (if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18) (if code%7776 = 3221 then 96 else 0)'
            weight_lemma=f'{profile}_simplified_{tag}'
        test=f'''(fun code => decide
      ({P}+min {R} (value {title}.{troot} (code%7776)) ≤
        {weight}+min {R} (value {title}.{sroot} (code/6))))'''
        text=''.join(f'import {x}\n' for x in imports)+f'''
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.PrefixCertificates102
open Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem {profile}_prefix_{tag} :
    checkPrefix {test} 6 0 {c['root']} = true := by decide +kernel

theorem {profile}_context_{tag} :
    contextCheck (weight {profile}Credit) {P} {title}.potential {di} {q} = true := by
  apply contextCheck_of_bounded_prefix {test}
    (weight {profile}Credit) {P} {title}.potential {di} {q} {c['cls']} block_{tag}.1
  · simpa only [block_{tag}.2] using {profile}_prefix_{tag}
  · intro code hc _
    have hs := {profile}_at_{sb} (code/6) (by omega)
    have ht := {profile}_at_{tb} (code%7776) (by omega)
    simp only [{weight_lemma}, source_{tag}, target_{tag}, hs, ht]

#print axioms {profile}_prefix_{tag}
#print axioms {profile}_context_{tag}
end Snake9.PrefixCertificates102
'''
        save(name,text)
        specs.append(dict(module=name,profile=profile,slope=P,range=R,role=role,
            direction=di,history=q,cls=c['cls'],root=c['root'],source_block=sb,target_block=tb,
            source_node=sroot,target_node=troot))
save('AllPotentialBlocks102', ''.join(f'import {g}\n' for g in groups)+''.join(f"import {c['module']}\n" for c in specs)+
    '\n#check Snake9.PrefixCertificates102.completed_context_10_0\n'+
    '#check Snake9.PrefixCertificates102.conditional_context_10_0\n')
out=dict(status='GENERATED_CANDIDATES_CHECK_RECEIPTS_FOR_CURRENT_STATUS',inputs_sha256=pins,
    blocks=blocks,root_modules=groups,specs=specs)
(HERE/'data/candidates.json').write_text(json.dumps(out,indent=2)+'\n')
print('GENERATED',len(groups),'root modules;',len(specs),'finite candidates')
