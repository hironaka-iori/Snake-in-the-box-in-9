"""Read frozen Git objects, check numerical value, and save explicit evidence gaps."""
import collections
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
BASE = '9043328966d65647acba6efd62f88eceb896622d'
MAIN = '4aca7255cd4715a16c98b313efc99e2ec7fbfdef'
LONG = '75404cc705135dd1f0526ecc9f1d198d3fbf0366'
PREFIX = 'milestones/10-window-aggregate/'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def blob(ref, path):
    return git('show', f'{ref}:{path}')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def save(name, data):
    p = HERE / 'data' / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(data, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')

def canon(ds):
    names = {}
    return tuple(names.setdefault(d, len(names)) for d in ds)

def matches(ds, alpha, record):
    shape = tuple(record['dirs'])
    for d, a in [(ds, alpha), (ds[::-1], alpha[::-1])]:
        if canon(d) == shape and all(lo <= x <= hi for x, (lo,hi) in zip(a, record['alpha'])):
            return True
    return False

def closure(target):
    roots = [ROOT/'work/final_lean', ROOT/'work/spectral/stronger', ROOT/'work/spectral',
             ROOT/'milestones/27-empty-square-packing/lean']
    found, missing = {}, set()
    def visit(m):
        if m in found or m in missing:
            return
        p = next((r/(m.replace('.', '/')+'.lean') for r in roots
                  if (r/(m.replace('.', '/')+'.lean')).exists()), None)
        if p is None:
            if not m.startswith(('Mathlib', 'Std', 'Lean', 'Init', 'Archive')):
                missing.add(m)
            return
        data = p.read_bytes()
        found[m] = dict(path=p.relative_to(ROOT).as_posix(), sha256=sha(data))
        for line in data.decode('utf-8').splitlines():
            if line.startswith('import '):
                for d in line.split('--')[0].split()[1:]:
                    visit(d)
    visit(target)
    return dict(target=target, existing_modules=found, missing_modules=sorted(missing))

def main():
    files = [PREFIX+'scripts/'+s for s in ['wincert.py','share_enc.py','verify_share_certs.py',
             'gen_share_wrapper.py','pipeline_231.sh']]
    files += [PREFIX+'data/share/'+s for s in ['final_a_X20.jsonl','final_a_X20.jsonl.cuts.json',
              'verify_a_X20.json','verify_b_X26.json']]
    files += ['work/spectral/stronger/EmptyShareBound.lean',
              'work/spectral/stronger/AggregateDirectionK6R34C7WShare231.lean']
    inventory=[]
    for p in files:
        data=blob(LONG,p)
        dst=HERE/'upstream'/p
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(data)
        inventory.append(dict(commit=LONG,path=p,sha256=sha(data),bytes=len(data)))
    # This is an exact upstream import, not a substitute corner-share definition.
    dest=ROOT/'work/spectral/stronger/EmptyShareBound.lean'
    data=blob(LONG,'work/spectral/stronger/EmptyShareBound.lean')
    if dest.exists() and dest.read_bytes()!=data:
        raise RuntimeError('Refusing to overwrite a changed EmptyShareBound source')
    dest.write_bytes(data)
    refs=git('for-each-ref','--format=%(objectname) %(refname:short)','refs/remotes').decode().splitlines()
    save('provenance.json',dict(base=BASE,main=MAIN,long_window=LONG,remote_snapshot=refs,files=inventory))

    # Numerics, retaining both endpoint counts (at least four) and window boundary losses.
    six_coef=21*6*9+2*21+735*6*2
    six_rhs=193494*6*2+21*6*59+2*21*7-903*6*2
    seven_coef=21*7*89+19*27+735*7*19
    seven_const=193494*7*19+19*27*8-903*7*19
    max_C=(seven_coef*231-seven_const-1)//147
    assert (six_coef,six_rhs,six_rhs//six_coef,max_C)==(9996,2318820,231,703)
    save('arithmetic.json',dict(packing=[dict(target_edges=e,loss=b,
        excluded_vertices=e+2,upper=221136+b,excluded_lhs=954*(e+2),
        contradiction_margin=954*(e+2)-(221136+b)) for e,b in [(231,1145),(230,191)]],
        six_centres=dict(coefficient=six_coef,rhs=six_rhs,bound=six_rhs//six_coef,
                         next_integer_margin=six_coef*232-six_rhs),
        seven_centres=dict(coefficient=seven_coef,rhs_without_C=seven_const,
                           C_coefficient=147,max_C_for_230=max_C,max_D_for_230=max_C-693,
                           D_status='NOT established by this audit')))

    # Stronger than checking only the two periodic examples: a finite abstract
    # witness survives the entire frozen five-centre exclusion index and packing cache.
    records=[]
    for fn in ['threshold_results.jsonl','ceiling_results.jsonl','probe_results.jsonl','refshare_results.jsonl']:
        for line in (ROOT/'milestones/27-empty-square-packing/upstream'/fn).read_text().splitlines():
            r=json.loads(line)
            if r.get('M',12)!=12 or len(r['dirs'])!=6:
                continue
            r['alpha']=r.get('alpha') or [(6,21) if s=='6+' else (int(s),int(s))
                                           for s in r['alpha_req'].split(',')]
            records.append(r)
    exclusion=json.loads((ROOT/(PREFIX+'data/direction_certificates_r4.json')).read_text())['cases']
    ds=[i%9 for i in range(232)]
    alpha=[4]+[5 if i%5==0 else 4 for i in range(1,232)]+[4]
    if sum(alpha)%2==0:
        alpha[116]+=1
    windows_checked=0
    for r in exclusion:
        k=len(r['alpha'])
        for j in range(len(ds)-k):
            assert not matches(ds[j:j+k+1],alpha[j+1:j+k+1],r), (j,r['case'])
            windows_checked+=1
    lower=[]
    for j in range(len(ds)-5):
        b=0
        for r in records:
            if matches(ds[j:j+6],alpha[j+1:j+6],r):
                assert r.get('status')!='UNSAT_MODEL'
                b=max(b,r['T'] if r.get('result')=='UNSAT' else r.get('min_lower',0))
        lower.append(b)
    assert not any(lower)
    T=sum(alpha); v=len(alpha); E=18428-2*T-70*v; G=24*T
    assert E>=0 and E%4==0 and G+840*v<=221136 and G+1145<114*v
    assert 42*232<=11*sum(alpha[1:-1])+291
    vertices=[0]
    for d in ds: vertices.append(vertices[-1]^(1<<d))
    first_repeat=next((i,j) for j in range(1,len(vertices)) for i in range(j) if vertices[i]==vertices[j])
    save('packing-counterexample.json',dict(scope='ABSTRACT SEQUENCE, NOT A SNAKE',m=232,v=v,
        directions=ds,alpha=alpha,corner_shares=[0]*v,E=E,s0=E//4,T=T,G=G,
        lost_corner_units=12*E,local_window_bounds=lower,
        exclusion_index_cases=len(exclusion),exclusion_window_tests=windows_checked,
        packing_input_records=len(records),packing231_required=114*v-1145,
        packing231_gap=114*v-1145-G,first_repeated_vertex_indices=first_repeat,
        conclusion='The saved packing cache plus five-centre count exclusions does not imply 231. '
                   'This does not refute the geometric charge conjecture or the six-centre route.'))
    for target in ['UpperBound237','UpperBound236','EmptyShareBound','SharePacking']:
        c=closure(target); save('closure-'+target+'.json',c)
        print(target,len(c['existing_modules']),'existing;',len(c['missing_modules']),'missing')
    index=json.loads(blob(LONG,PREFIX+'data/direction_certificates_k6.json'))
    sets={}
    for filename in ['minimal_L7_k6_K7_r3_r34.json','minimal_L8_k7_K7_r3_89_19.json']:
        d=json.loads(blob(LONG,PREFIX+'data/'+filename))
        def key(r): return (canon(r['dirs']),tuple(map(tuple,r['alpha'])),r.get('radius',3))
        verified={key(r) for r in index['cases'] if r.get('drat_trim_verified')}
        need={key(r) for r in d['exclusions']}
        sets[filename]=dict(required=len(need),exact_key_recorded_verified=len(need&verified),
            exact_key_missing=len(need-verified),note='Exact keys only; stronger interval reuse is not inferred.')
    save('certificate-inventory.json',dict(index_entries=len(index['cases']),sets=sets,
        parallel_share_six=json.loads(blob(LONG,PREFIX+'data/share/verify_a_X20.json')),
        parallel_share_seven=json.loads(blob(LONG,PREFIX+'data/share/verify_b_X26.json'))))
    print('Arithmetic and abstract packing witness PASS; no unconditional target asserted.')

if __name__=='__main__': main()
