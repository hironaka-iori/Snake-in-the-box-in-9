"""Record bounded search outcomes without interpreting timeouts as exclusions."""
from pathlib import Path
import hashlib,json,collections
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[]
independent={r['width']:r for r in json.loads((H/'data/independent-containment.json').read_bytes())['widths']}
for source in sorted((H/'data').glob('regions*.json')):
    data=json.loads(source.read_bytes());w=data['width'];p=H/'data'/f'pair{w}.json'
    if not p.exists():continue
    run=json.loads(p.read_bytes());execution=p.with_name(f'pair{w}-execution.json');rec=json.loads(execution.read_bytes())
    assert rec['status']=='ACCEPTED_NATIVE_RESULT' and rec['stop_reason'] is None
    assert sha(p)==rec['result_sha256'] and all(sha(x)==v for x,v in rec['pins'].items())
    assert all(sha(x)==v for x,v in data['pins'].items())
    assert len({r['id'] for r in run['results']})==len(run['results'])
    statuses=dict(collections.Counter(r['status'] for r in run['results']))
    unresolved=[r['id'] for r in run['results'] if r['status'] not in ['INHERITED_EXCLUDED','STATIC_EXCLUDED','INFEASIBLE','WITNESS']]
    split_excluded=[]
    if w==42:
        splits=[]
        for tag,count in [('split42-zero',0),('split42-two',2)]:
            sp=H/'data'/(tag+'.json');ep=sp.with_name(tag+'-execution.json')
            sr=json.loads(sp.read_bytes());er=json.loads(ep.read_bytes())
            assert er['status']=='ACCEPTED_NATIVE_RESULT' and er['stop_reason'] is None
            assert sha(sp)==er['result_sha256'] and all(sha(x)==v for x,v in er['pins'].items())
            assert sr['arguments']['first_crossings']==count and sr['arguments']['width']==42
            assert {r['id'] for r in sr['results']}==set(unresolved) and len(sr['results'])==len(unresolved)
            splits.append({r['id']:r['status'] for r in sr['results']})
        for i in unresolved:
            context=data['contexts'][i]
            assert context['replacement_crossings']==2
            assert all((a^b)&256==0 for a,b in [x['anchors'] for x in context['parts']])
            if all(s[i]=='INFEASIBLE' for s in splits):split_excluded.append(i)
        unresolved=[i for i in unresolved if i not in split_excluded]
        combined=dict(contexts=[dict(r,combined_status='SPLIT_EXCLUDED' if r['id'] in split_excluded else r['status']) for r in run['results']],split_excluded=split_excluded,unresolved=unresolved,pins={str(H/'data'/(tag+suffix)):sha(H/'data'/(tag+suffix)) for tag in ['pair42','split42-zero','split42-two'] for suffix in ['.json','-execution.json']})
        (H/'data/combined42.json').write_text(json.dumps(combined,indent=2)+'\n',encoding='utf-8')
    missing=sorted(set(range(len(data['contexts'])))-{r['id'] for r in run['results']})
    rows.append(dict(width=w,contexts=len(data['contexts']),initial_statuses=statuses,split_excluded=split_excluded,unresolved=unresolved,missing=missing,witness=run['witness'],complete_exclusion=not unresolved and not missing and not run['witness'],seconds=run['seconds'],result_sha256=sha(p),execution_sha256=sha(execution),input_sha256=sha(source)))
summary=dict(round=225,widths=rows,complete_through=max([33]+[r['width'] for r in rows if r['complete_exclusion']]),first_unresolved=min([r['width'] for r in rows if r['unresolved'] or r['missing']],default=None),solver_exclusions_lean_certified=False,scope='Specified normalized191-edge seed, two equal-length replacements retaining outside indices/anchors, endpoint24 extension, exactlyfour bit8crossings. No global upper bound; no claim about other seeds/endpoints or more replacement regions.')
(H/'data/search-summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(json.dumps(summary,indent=2))
