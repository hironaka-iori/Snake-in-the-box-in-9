"""Independent witness, exchange, provenance and theorem-receipt audit."""
import json,collections
from pathlib import Path
from exchange import ROOT,HERE,parents,transforms,sha,check
def valid(p):
    if len(set(p))!=len(p):return False
    return all(((p[i]^p[j]).bit_count()==1)==(i+1==j) for j in range(len(p)) for i in range(j))
def main():
    a,b=parents();ex=json.loads((HERE/'data/exchanges.json').read_text())
    assert ex['script_sha256_lf']==sha(HERE/'scripts/exchange.py')
    ts=list(transforms(b));assert len(ts)==5760
    assert len({(tuple(p),s) for p,s,q in ts})==5760
    qs={i:q for i,(_,_,q) in enumerate(ts)}
    assert ex['valid_exchanges']==5760 and ex['best_edges']==190
    for row in ex['alignments']:
        i=row['index'];p,s,q=ts[i]
        assert p==row['permutation'] and s==row['swap']
        assert q[0]==41 and q[-1]==67 and len(set(q))==191
        assert len(set(a)&set(q))==row['overlap']
        assert len(set(a)|set(q))==row['union_size']
    for r in ex['exchanges']:
        assert r['cut_indices']==[0,186] and r['donor_indices']==[0,190] and r['edges']==190
    # Independent direct pair testing on twenty evenly spaced alignments.
    audited=[]
    for index in sorted({i*5759//19 for i in range(20)}):
        q=qs[index];pos={v:i for i,v in enumerate(q)};found=[]
        for i,u in enumerate(a):
            if u not in pos:continue
            for j in range(i+1,len(a)):
                if a[j] not in pos:continue
                s,t=pos[u],pos[a[j]]
                if abs(t-s)<=j-i:continue
                mid=q[min(s,t)+1:max(s,t)]
                if s>t:mid=mid[::-1]
                child=a[:i+1]+mid+a[j:]
                if valid(child):found.append([i,j,s,t])
        assert found==[[0,186,0,190]];audited.append(index)
    union=json.loads((HERE/'data/union-search.json').read_text())
    assert union['script_sha256_lf']==sha(HERE/'scripts/union_search.py')
    assert union['exchange_sha256_lf']==sha(HERE/'scripts/exchange.py')
    assert union['model_sha256_lf']==sha(ROOT/'work/neighborhood_search.py')
    assert len(union['runs'])==36 and len(union['selected_alignments'])==12
    for r in union['controls']:
        check(r['path_vertices']);assert len(r['path_vertices'])==r['edges']+1
    for r in union['runs']:
        assert r['union_size']==len(set(a)|set(qs[r['alignment']]))
        assert r['status']==('INFEASIBLE' if r['retain_intersection'] else 'UNKNOWN')
    de=json.loads((HERE/'data/double-exchanges.json').read_text())
    assert de['script_sha256_lf']==sha(HERE/'scripts/double_exchange.py')
    double_count=0;paths=set()
    for row in de['rows']:
        q=qs[row['alignment']]
        def mid(s,t):
            r=q[min(s,t)+1:max(s,t)]
            return r if s<t else r[::-1]
        for r in row['valid']:
            (i,j),(k,l)=r['cuts'];(s,t),(u,v)=r['donor_cuts']
            p=a[:i+1]+mid(s,t)+a[j:k+1]+mid(u,v)+a[l:]
            check(p);assert p==q and r['edges']==190
            double_count+=1;paths.add(tuple(p))
    div=json.loads((HERE/'data/diversity.json').read_text())
    assert div['script_sha256_lf']==sha(HERE/'scripts/diversify.py')
    for r in div['runs']:
        check(r['path_vertices']);assert r['path_vertices']==qs[r['alignment']]
        assert r['objective']==0 and r['status']=='FEASIBLE'
    log=(HERE/'logs/join.log').read_text(encoding='utf-8-sig')
    assert 'sorryAx' not in log and 'error:' not in log
    assert log.count('depends on axioms:')==3 and log.count('does not depend on any axioms')==1
    files=[p for folder in ('scripts','lean','data','logs') for p in (HERE/folder).glob('*') if p.is_file() and p.name!='verification.json']
    files += [ROOT/'milestones/19-coordinate-face-repair/data/two-arm-seed186.json',ROOT/'milestones/20-middle-path-release/data/paired-seed190.json',ROOT/'work/neighborhood_search.py',ROOT/'work/final_lean/Snake9.lean',ROOT/'paper/snake9_research.tex']
    report={'status':'PASSED','single_exchange_direct_audit_alignments':audited,'single_exchange_total_positive_candidates':ex['positive_gain_candidates'],'double_exchange_positive_pairs':sum(r['positive_pairs'] for r in de['rows']),'double_exchange_valid':double_count,'double_exchange_distinct_paths':len(paths),'union_outcomes':dict(collections.Counter(r['status'] for r in union['runs'])),'lean_audits':4,'sha256_lf':{p.relative_to(ROOT).as_posix():sha(p) for p in files},'limitations':'Full census remains ordinary computation; twenty single-exchange alignments independently rechecked. Solver exclusions have no Lean certificates. No improved record.'}
    (HERE/'data/verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k!='sha256_lf'},indent=2))
if __name__=='__main__':main()
