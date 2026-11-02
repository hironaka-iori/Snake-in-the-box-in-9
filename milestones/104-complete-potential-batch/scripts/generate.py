"""Prepare a complete grouped certificate batch, or assemble its checked results."""
from pathlib import Path
import argparse, ast, hashlib, json

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parser=argparse.ArgumentParser();parser.add_argument('--assemble',action='store_true');args=parser.parse_args()
assert not (HERE/'data/check.lock').exists()
cp=ROOT/'milestones/101-context-specialization/data/generated-contexts.json'
bp=ROOT/'milestones/102-potential-block-reduction/data/candidates.json'
sp=ROOT/'milestones/103-joint-potential-traversal/data/checkpoint.json'
gp=ROOT/'milestones/103-joint-potential-traversal/data/group-analysis.json'
ap=ROOT/'milestones/92-full-witness-batch/lean/ContextAssignmentData.lean'
contexts=read(cp)['contexts']; indexed={(c['direction'],c['history']):(i,c) for i,c in enumerate(contexts)}
blocks=read(bp)['blocks'];prior=read(sp);groups=read(gp)['profiles']
entries=ast.literal_eval(next(l for l in ap.read_text().splitlines() if l.startswith('def savedBlockClasses :')).split(':=',1)[1].strip())
assert len(entries)==791 and {(b//75,b%75,cl) for b,cl in entries}=={(c['direction'],c['history'],c['cls']) for c in contexts}
inputs={p.relative_to(ROOT).as_posix():sha(p) for p in [cp,bp,sp,gp,ap]}

def save(name,source):
    path=HERE/'lean'/(name+'.lean')
    if path.exists() and path.read_text(encoding='utf-8')==source:return
    assert not (HERE/'data'/(name+'-audit.json')).exists(),name
    path.write_text(source,encoding='utf-8')

existing=[]
for c in prior['complete_contexts']:
    p=c['profile'];tag=f"{c['direction']}_{c['history']}";n=c['origin_milestone']
    theorem=f'Snake9.PrefixCertificates{n}.{p}_context_'+('reduced' if n==100 else tag)
    existing.append(dict(profile=p,direction=c['direction'],history=c['history'],
        module=c['module'],theorem=theorem,origin_milestone=n,accepted_edges=c['accepted_edges']))
known={(x['profile'],x['direction'],x['history']) for x in existing}

if args.assemble:
    plan=read(HERE/'data/plan.json');assert plan['inputs_sha256']==inputs
    selected=[]
    for g in plan['groups']:
        choices=[x for x in g['variants'] if (HERE/'data'/(x['module']+'-audit.json')).exists()]
        assert choices,('Unchecked group',g['profile'],g['index'])
        choice=choices[0];name=choice['module'];r=read(HERE/'data'/(name+'-audit.json'))
        assert r['status']=='PASS_COMPLETE_BATCH_MODULE' and not r['timeout'] and r['exit_code']==0
        assert sha(HERE/'lean'/(name+'.lean'))==r['source_sha256']
        assert sha(HERE/'build'/(name+'.olean'))==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
        selected.append(dict(profile=g['profile'],index=g['index'],module=name,
            method=choice['method'],contexts=g['contexts']))
    for p,P in [('completed',483),('conditional',496)]:
        title=p.title();sources={};imports={'GraphAssembly104'}
        for c in existing:
            if c['profile']==p:
                imports.add(c['module']);sources[(c['direction'],c['history'])]=c['theorem']
        for g in selected:
            if g['profile']==p:
                imports.add(g['module'])
                for di,q in g['contexts']:
                    assert (di,q) not in sources
                    sources[(di,q)]=f"Snake9.{g['module']}.{p}_context_{di}_{q}"
        assert set(sources)==set(indexed)
        literal='['+','.join(f'({b},{cl})' for b,cl in entries)+']'
        text=''.join(f'import {m}\n' for m in sorted(imports))+f'''
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.Complete104
open Snake9.GraphAssembly104 Snake9.PotentialChecker99 Snake9.Batch92
open Snake9.Weights98 Snake9.CountFree98 Snake9.Potential99

theorem {p}_saved (entry : Nat × Nat) (h : entry ∈ savedBlockClasses) :
    contextCheck (weight {p}Credit) {P} {title}.potential (entry.1/75) (entry.1%75) = true := by
  change entry ∈ {literal} at h
  simp only [List.mem_cons, List.mem_singleton] at h
  rcases h with '''+' | '.join(['rfl']*len(entries))+'\n'
        text+=''.join(f'  · exact {sources[(b//75,b%75)]}\n' for b,_ in entries)
        text+=f'''
theorem {p}_graph : graphCheck (weight {p}Credit) {P} {title}.potential = true :=
  graphCheck_of_saved_blocks _ _ _ {p}_saved

#print axioms {p}_saved
#print axioms {p}_graph
end Snake9.Complete104
'''
        save('All'+title+'104',text)
    (HERE/'data/assembly-selection.json').write_text(json.dumps(dict(status='GENERATED_ASSEMBLY_AWAITING_LEAN',groups=selected),indent=2)+'\n')
    print('GENERATED full graph assemblies; both require Lean checks')
    raise SystemExit

planned=[]
for p,P,R in [('completed',483,551),('conditional',496,602)]:
    title=p.title()
    for gi,g in enumerate(groups[p]['groups']):
        pending=[(di,q) for di,q in g['contexts'] if (p,di,q) not in known]
        if not pending:continue
        cache=next(((di,q) for di,q in g['contexts'] if q==0 and di in [0,1,9,10]),None)
        representative=cache or pending[0]
        _,c=indexed[representative]
        sb,tb=c['source_base']//7776,c['target_base']//7776
        sroot,troot=blocks[p][sb],blocks[p][tb]
        selected='['+','.join(c['selected'])+']'
        weight=f"120*(code%6+1)+max (max {c['geometric']} (emittedCredit {selected} code)) (max ({c['conditioned']}) {c[p]})"
        test=f'''(fun code => decide
      ({P}+min {R} (value {title}.{troot} (code%7776)) ≤
        {weight}+min {R} (value {title}.{sroot} (code/6))))'''
        method='reuse' if cache else prior['provisional_batch_method_by_profile'][p]
        methods=[method] if cache else [method,'joint' if method=='baseline' else 'baseline']
        variants=[]
        for vi,m in enumerate(methods):
            name=f'{title}{"Batch" if vi==0 else "Alternative"}104G{gi:03d}'
            imports={'JointTraversal103','BoundedPrefixTransfer102'}
            if cache:imports.add(f'{title}Block102D{cache[0]}Q{cache[1]}')
            for di,q in pending:
                index,row=indexed[(di,q)]
                imports.add(f'Context101Group{index//64:02d}')
                imports.add(f"PotentialRoots102Group{(row['source_base']//7776)//52:02d}")
                imports.add(f"PotentialRoots102Group{(row['target_base']//7776)//52:02d}")
            text=''.join(f'import {x}\n' for x in sorted(imports))+f'''
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.{name}
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79
'''
            if m=='joint':
                text+=f'''
theorem joint_checked : checkJoint (fun code => {weight}) {P} {R} 6 0 {c['root']}
    {title}.{sroot} {title}.{troot} = true := by decide +kernel
'''
            text+=f'\ntheorem prefix_checked : checkPrefix {test} 6 0 {c["root"]} = true := by\n'
            if m=='joint':text+=f'  exact joint_root_prefix _ {P} {R} {c["root"]} {title}.{sroot} {title}.{troot} joint_checked\n'
            elif m=='reuse':text+=f'  exact Snake9.PrefixCertificates102.{p}_prefix_{cache[0]}_{cache[1]}\n'
            else:text+='  decide +kernel\n'
            for di,q in pending:
                _,row=indexed[(di,q)];tag=f'{di}_{q}'
                rs,rt=row['source_base']//7776,row['target_base']//7776
                assert blocks[p][rs]==sroot and blocks[p][rt]==troot and row['root']==c['root']
                text+=f'''
theorem {p}_context_{tag} :
    contextCheck (weight {p}Credit) {P} {title}.potential {di} {q} = true := by
  apply contextCheck_of_bounded_prefix {test}
    (weight {p}Credit) {P} {title}.potential {di} {q} {row['cls']} block_{tag}.1
  · simpa only [block_{tag}.2] using prefix_checked
  · intro code hc _
    have hs := {p}_at_{rs} (code/6) (by omega)
    have ht := {p}_at_{rt} (code%7776) (by omega)
    simp only [{p}_{tag}, source_{tag}, target_{tag}, hs, ht]

#print axioms {p}_context_{tag}
'''
            text+='\n#print axioms prefix_checked\n'
            if m=='joint':text+='#print axioms joint_checked\n'
            text+=f'end Snake9.{name}\n'
            save(name,text)
            variants.append(dict(module=name,method=m,source_sha256=sha(HERE/'lean'/(name+'.lean'))))
        planned.append(dict(profile=p,index=gi,contexts=pending,representative=representative,
            variants=variants,acceptance_root=c['root'],source_node=sroot,target_node=troot,
            slope=P,range=R))
planned.sort(key=lambda g:(g['variants'][0]['method']!='reuse',min(d for d,_ in g['contexts']),g['profile'],g['index']))
out=dict(status='GENERATED_COMPLETE_BATCH_AWAITING_LEAN',inputs_sha256=inputs,existing=existing,groups=planned,
    contexts_per_profile=791,expected_pending_profile_contexts=1570,
    scope='Generated expressions and reuse groups are proposals. Only successful Lean receipts count as certificates.')
assert sum(len(g['contexts']) for g in planned)==1570
path=HERE/'data/plan.json'
if path.exists():assert read(path)==out,'Existing plan differs; preserve it before a deliberate revision.'
else:path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('GENERATED',len(planned),'groups;',sum(len(g['variants']) for g in planned),'candidate modules;',sum(g['variants'][0]['method']=='reuse' for g in planned),'reuse groups; 1570 pending profile/contexts')
