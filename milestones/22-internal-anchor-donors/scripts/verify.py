"""Check inputs, sampled enumeration decisions, saved defects and Lean receipts."""
import json
from pathlib import Path
from search import ROOT,HERE,sources,choose_pairs,alignments,sha,check
def is_snake(p):
    return len(set(p))==len(p) and all(((p[i]^p[j]).bit_count()==1)==(i+1==j) for j in range(len(p)) for i in range(j))
def main():
    data=json.loads((HERE/'data/search.json').read_text());a,b=sources()
    assert data['script_sha256_lf']==sha(HERE/'scripts/search.py')
    assert data['source_core_sha256_lf']==sha(ROOT/'work/final_lean/Snake9.lean')
    assert data['recipient_sha256_lf']==sha(ROOT/'milestones/19-coordinate-face-repair/data/two-arm-seed186.json')
    assert data['donor_vertices']==b and b[0]==41 and b[190]==67 and b[-1]==83
    assert [tuple(r['anchor_pair']) for r in data['reports']]==choose_pairs(b)
    assert len(data['witnesses'])==0
    samples=[];checked_candidates=0
    for pair in choose_pairs(b):
        seen=set()
        for index,(perm,swap,q) in enumerate(alignments(b,*pair)):
            assert sorted(perm)==list(range(9))
            seen.add((tuple(perm),swap))
            if index not in (0,1000,3000,5759):continue
            check(q);pos={v:i for i,v in enumerate(q)};anchors=[i for i,v in enumerate(a) if v in pos]
            for ai,i in enumerate(anchors):
                for j in anchors[ai+1:]:
                    u,v=pos[a[i]],pos[a[j]]
                    if 186+abs(v-u)-(j-i)<192:continue
                    interior=q[min(u,v)+1:max(u,v)]
                    if u>v:interior.reverse()
                    child=a[:i+1]+interior+a[j:]
                    assert not is_snake(child);checked_candidates+=1
                u=pos[a[i]]
                for prefix in (a[:i+1],a[i:][::-1]):
                    for tail in (q[u+1:],q[:u][::-1]):
                        child=prefix+tail
                        if len(child)<193:continue
                        assert not is_snake(child);checked_candidates+=1
            samples.append({'pair':pair,'alignment':index})
        assert len(seen)==5760
    for row in data['near_candidates']:
        p=row['path_vertices'];assert len(p)==len(set(p))==197
        assert all((v^w).bit_count()==1 for v,w in zip(p,p[1:]))
        chords=[[i,j] for j in range(len(p)) for i in range(j-1) if (p[i]^p[j]).bit_count()==1]
        assert chords==row['chords'] and len(chords)>0
    logs={}
    for name,expected in [('paired-seed.log',10),('full-donor.log',4)]:
        s=(HERE/'logs'/name).read_text(encoding='utf-8-sig')
        assert 'sorryAx' not in s and 'error:' not in s
        assert s.count('depends on axioms:')==expected;logs[name]=expected
    files=[p for f in ['scripts','lean','logs','data'] for p in (HERE/f).glob('*') if p.is_file() and p.name!='verification.json']
    report={'status':'PASSED','alignments':23040,'direct_audit':samples,'direct_candidates_rejected':checked_candidates,'lean_audits':logs,'minimum_saved_chords':min(len(r['chords']) for r in data['near_candidates']),'scope':'Independent direct checks on sixteen alignments; complete census remains ordinary computation, not a Lean certificate. Saved near candidates are invalid walks.','sha256_lf':{p.relative_to(ROOT).as_posix():sha(p) for p in files}}
    (HERE/'data/verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('sha256_lf','direct_audit')},indent=2))
if __name__=='__main__':main()
