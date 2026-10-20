"""Compare the retained-vertex constraint with exhaustive Q3 path subsets."""
import json
from pathlib import Path
import protected
from search import all_path_sets,sha,HERE,solve
def main():
    seed=[0,1,3,7,6];seedmask=sum(1<<v for v in seed);paths=all_path_sets(3);rows=[]
    for required in [1,6]:
        protected.protected_vertex=required
        for region in range(0,256,4):
            outside=255^region
            for target in [4,5]:
                valid=[p for p in paths if p.bit_count()==target+1 and
                    p&outside==seedmask&outside and p>>required&1]
                expected=max(((p&~seedmask).bit_count() for p in valid),default=None)
                r=solve(3,seed,{v for v in range(8) if region>>v&1},target,3)
                if expected is None:assert r['status']=='INFEASIBLE'
                else:
                    assert r['status']=='OPTIMAL' and r['objective_new_vertices']==expected
                    assert required in r['path_vertices']
                rows.append(dict(required=required,region=region,target=target,expected=expected,
                    status=r['status'],actual=r.get('objective_new_vertices')))
    report=dict(status='PASSED',cases=rows,script_sha256_lf=sha(Path(__file__)),
        protected_sha256_lf=sha(HERE/'scripts/protected.py'),search_sha256_lf=sha(HERE/'scripts/search.py'))
    (HERE/'data/protected-controls.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(f'Passed {len(rows)} protected-vertex controls')
if __name__=='__main__':main()
