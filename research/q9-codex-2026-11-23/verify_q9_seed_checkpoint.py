"""Collect completed local runs and independently validate the record lower witness."""
from pathlib import Path
from itertools import combinations
from math import factorial
import hashlib,json
here=Path(__file__).resolve().parent
def last(name):
    p=here/name
    if not p.is_file():return ''
    return next((s for s in reversed(p.read_text().splitlines()) if s),'')
def unique_words(name):
    return sorted(set((here/name).read_text().split()))
def check_path(points):
    assert len(set(points))==len(points) and all(0<=v<512 for v in points)
    for i,x in enumerate(points):
        for j in range(i):
            assert ((x^points[j]).bit_count()==1)==(i==j+1)
def main():
    paths=unique_words('q8_catalogue_96_98.words')
    assert len(paths)==753
    expected=len(paths)*(len(paths)+1)//2
    certificate=json.loads((here/'q8_catalogue_lifts_verified.json').read_text())['lower_certificate']
    witness=certificate['vertices'];check_path(witness);assert len(witness)==192
    checks=[l.split() for l in (here/'q9_seed_growth_claw_controls.log').read_text().splitlines()]
    assert {(int(d),int(e)) for _,d,e,_,_ in checks}=={(d,e) for d in [3,4] for e in range(6)}
    assert all(int(n)==1000 and 0<int(pos)<int(n) for _,_,_,n,pos in checks)
    planted=(here/'q9_seed_growth_planted.log').read_text().splitlines()
    assert [int(l.split()[1]) for l in planted]==list(range(10))
    results=[]
    for e,tag in [(3,'three'),(4,'four'),(5,'five')]:
        for goal in range(192,197):
            run=f'q8_all_{goal}_{tag}_seed_growth.log'
            alternate=f'q8_clustered_hosts_plus_{tag}_{goal}.log'
            replay=f'q8_clustered_independent_{tag}_{goal}.log'
            completed={}
            for label,name in [('seed',run),('refill',alternate),('independent',replay)]:
                line=last(name)
                if not line.startswith('DONE '):continue
                fields=list(map(int,line.split()[1:]))
                if label=='independent':
                    g,ext,pairs,eligible,wins=fields
                    assert g==goal and ext==e and pairs==expected and wins==0
                else:
                    g,groups,pairs,tested,eligible,nodes=fields
                    assert g==goal and groups==1653 and pairs==expected and eligible<=tested
                completed[label]={'file':name,'eligible':eligible}
            if completed:
                assert len({r['eligible'] for r in completed.values()})==1
                results.append({'edges':goal,'outside_at_most':e,'finished_negative_runs':completed})
    r={'dataset_sha256':hashlib.sha256((here/'q8_catalogue_96_98.words').read_bytes()).hexdigest(),
       'paired_catalogue_entries':expected,'labelled_relative_placements':expected*256*factorial(8),
       'known_witness_edges':len(witness)-1,'independent_hamming_pairs':len(witness)*(len(witness)-1)//2,
       'bruteforce_agreements':sum(int(l[3]) for l in checks),'planted_outside_counts':list(range(10)),
       'completed':results}
    selected=[]
    for m in (191,190,189):
        name=f'q8_all_retain{m}_unbounded.log'
        row=last(name).split()
        if row and row[0]=='DONE':
            _,g,groups,pairs,tested,kept,nodes=row
            assert int(g)==192 and int(groups)==1653 and int(pairs)==expected
            selected.append({'minimum_host_vertices':m,'maximum_outside_vertices':'all available','negative_run':name,'eligible_placements':int(kept)})
    r['unrestricted_outside_completed']=selected
    r['unrestricted_small_agreements']=sum(int(l.split()[3]) for l in (here/'q9_retained_small.log').read_text().splitlines() if l.startswith('MATCH '))
    assert r['unrestricted_small_agreements']==12000
    print(json.dumps(r,indent=2))
if __name__=='__main__':main()
