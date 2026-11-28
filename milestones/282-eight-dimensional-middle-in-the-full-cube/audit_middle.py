"""Replay full-cube findings and independently list every possible occupancy of the original face."""
from collections import Counter
from importlib.util import module_from_spec,spec_from_file_location
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
from middles import BASE,HERE,check,read,rebuild,save,shape
from returns import cases,lower_formula,old_shapes

spec=spec_from_file_location('certificate_audit280',next(HERE.parent.glob('280-*'))/'audit.py')
audit=module_from_spec(spec)
spec.loader.exec_module(audit)


def upper_patterns(m):
    occupied=set(m)
    candidates=[]
    for v in set(range(256))-occupied:
        near=[j for j,w in enumerate(m) if (v^w).bit_count()==1]
        if not near or (len(near)==1 and near[0] in (0,len(m)-1)):
            candidates.append(v)
    undominated=sorted(v for v in candidates if all((v^w).bit_count()>1 for w in m))
    assert all((v^w).bit_count()>=2 for v,w in combinations(undominated,2))
    patterns=set()
    for mask in range(1<<len(candidates)):
        sites=occupied|{v for j,v in enumerate(candidates) if mask>>j&1}
        adj={w:[v for v in sites if (v^w).bit_count()==1] for w in sites}
        if any(len(nb)>2 for nb in adj.values()):
            continue
        isolated=tuple(sorted(w for w,nb in adj.items() if not nb))
        if len(isolated)>2:
            continue
        ends=[v for v,nb in adj.items() if len(nb)==1]
        if len(ends)!=2:
            continue
        run=[ends[0]]
        for w in run:
            run.extend(v for v in adj[w] if v not in run)
        if len(run)+len(isolated)!=len(sites):
            continue
        if not any(run[j:j+len(m)]==m for j in range(len(run)-len(m)+1)):
            run.reverse()
        assert any(run[j:j+len(m)]==m for j in range(len(run)-len(m)+1))
        patterns.add((tuple(run),isolated))
    return undominated,patterns


def main():
    geo=read(HERE/'geometry.json')
    direct=read(HERE/'full-192.json')
    f191=HERE/'full-191.json'
    lower=read(f191) if f191.exists() else {}
    fpart=HERE/'returns.json'
    split=read(fpart) if fpart.exists() else {}
    fbranch=HERE/'neighbours.json'
    children=read(fbranch) if fbranch.exists() else {}
    old=old_shapes(geo)
    bank=read(HERE.parents[1]/'work/bank9.json')
    bank_words={shape(r['vertex_sequence']) for r in bank}
    archive_hits={}
    shape_ids={shape(r['middle']):k for k,r in geo.items()}
    for i,b in enumerate(bank):
        p=b['vertex_sequence']
        check(p)
        for n in {len(w) for w in shape_ids}:
            for j in range(len(p)-n):
                key=shape_ids.get(shape(p[j:j+n+1]))
                if key is not None:
                    archive_hits.setdefault(key,[i,j])
    rows={}
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        verifier,_=rebuild.masks.compilers(scratch)
        for k,r in geo.items():
            m=r['middle']
            U,patterns=upper_patterns(m)
            assert U==r['undominated'] and patterns=={(tuple(p['run']),tuple(p['terminal_returns'])) for p in r['patterns']}
            audit.audit_geometry(m)
            ceiling=None
            floor=191 if k in archive_hits else r['archived_lower']
            new=False
            for a in lower.get(k,{}).values():
                audit.replay_case(m,a,HERE,scratch,verifier)
                if a['status']=='witness':
                    floor=191
                    new=shape(a['path']) not in bank_words
                if a['status']=='excluded':
                    ceiling=190
            summary={}
            for maj in (0,1):
                row=direct[k][str(maj)]
                audit.replay_case(m,row,HERE,scratch,verifier)
                if row['status']=='excluded':
                    summary[str(maj)]=dict(excluded=True,method='full-cube proof')
                    continue
                if row['status']=='witness':
                    assert ceiling is None
                    floor=192
                    summary[str(maj)]=dict(excluded=False,method='witness')
                    continue
                outcomes={}
                for tag,run,t,dep,tips,rule in cases(r,old,maj):
                    if rule:
                        outcomes[tag]=rule
                        continue
                    a=split.get(k,{}).get(tag,{})
                    state=a.get('status','open')
                    if state=='excluded':
                        f,_=lower_formula(run,t,dep,tips,maj,a['cycles'])
                        cnf=scratch/'face.cnf'
                        assert f.save(cnf)==a['cnf_sha256']
                        assert rebuild.masks.p.check_proof(cnf,HERE/'return-proofs'/a['proof'],verifier)==a['replay']
                    elif state=='witness':
                        check(a['path'])
                        floor=192
                    elif tag in children.get(k,{}):
                        from neighbours import replay
                        state=replay(run,t,dep,tips,maj,children[k][tag],scratch,verifier)
                    if state=='open' and len(dep)==1 and 192-(len(run)-1)-1-len(t)>98:
                        state='opposite arm exceeds the proved eight-cube maximum'
                    outcomes[tag]=state
                summary[str(maj)]=dict(excluded=all(s not in ('open','witness') for s in outcomes.values()),branches=outcomes)
            if all(s['excluded'] for s in summary.values()) and ceiling is None:
                ceiling=191
            assert ceiling is None or floor<=ceiling
            rows[k]=dict(source=r['archived_source'],edges=len(m)-1,undominated=U,patterns=len(patterns),
                         lower=floor,upper=ceiling,bank_191_example=archive_hits.get(k),parities=summary,new_191_vs_bank=new)
    out=dict(shapes=len(rows),undominated_site_counts=Counter(len(r['undominated']) for r in rows.values()),
             upper_face_patterns=sum(r['patterns'] for r in rows.values()),
             excluded_192=sum(r['upper'] is not None and r['upper']<192 for r in rows.values()),
             exact_maxima=Counter(r['upper'] for r in rows.values() if r['lower']==r['upper']),
             new_191_shapes=len({shape(a['path']) for k,c in lower.items() for a in c.values()
                                if a['status']=='witness' and shape(a['path']) not in bank_words}),
             rows=rows)
    save(HERE/'coverage.json',out)
    print(out['shapes'],'shapes;',out['upper_face_patterns'],'upper patterns;',out['excluded_192'],'excluded 192; exact',out['exact_maxima'],'new 191',out['new_191_shapes'])


if __name__=='__main__':
    main()
