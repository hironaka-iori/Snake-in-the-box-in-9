"""Independent checks: source provenance, saved local witnesses, and packing certificates."""
import hashlib,itertools,json
from fractions import Fraction as F
from pathlib import Path
HERE=Path(__file__).resolve().parents[1]
ROOT=HERE.parents[1]

def statistics(S):
    pairs=list(itertools.combinations(range(9),2))
    degree={q:sum((q^(1<<a)) in S for a in range(9)) for q in range(512)}
    empty={q:sum(not S.intersection((q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b))) for a,b in pairs) for q in range(512)}
    alpha={x:sum(not S.intersection((x^(1<<a),x^(1<<b),x^(1<<a)^(1<<b))) for a,b in pairs) for x in S}
    share={x:sum(12*empty[x^(1<<a)]//degree[x^(1<<a)] for a in range(9)) for x in S}
    return degree,empty,alpha,share

def main():
    manifest=json.loads((HERE/'data/provenance.json').read_text())
    for r in manifest['files']:
        assert hashlib.sha256((HERE/r['saved']).read_bytes().replace(b'\r\n',b'\n')).hexdigest()==r['sha256_lf']
    checked=0
    for fn in ['ceiling_results.jsonl','probe_results.jsonl']:
        for line in (HERE/'upstream'/fn).read_text().splitlines():
            r=json.loads(line)
            if 'sel' not in r or r.get('M',12)!=12:continue
            S=set(r['sel']); assert len(S)==len(r['sel'])
            win=[0]
            for a in r['dirs']:win.append(win[-1]^(1<<a))
            assert set(win)<=S
            B={v for v in range(512) if min((v^x).bit_count() for x in win[1:-1])<=4}
            assert S<=B
            deg,empty,alpha,share=statistics(S)
            assert all(deg[x]<=2 for x in S)
            interior={x for x in S if all((x^(1<<a)) in B for a in range(9))}
            assert all(deg[x]>=1 for x in interior)
            assert sum(deg[x]==1 for x in interior)<=2
            unseen=set(S)
            while unseen:
                todo=[next(iter(unseen))];component=set()
                while todo:
                    v=todo.pop()
                    if v not in unseen:continue
                    unseen.remove(v);component.add(v)
                    todo += [v^(1<<a) for a in range(9) if (v^(1<<a)) in unseen]
                assert sum(deg[x] for x in component)==2*(len(component)-1)
            bounds=r.get('alpha') or [(6,21) if x=='6+' else (int(x),int(x)) for x in r['alpha_req'].split(',')]
            for c,(lo,hi) in zip(win[1:-1],bounds):assert lo<=alpha[c]<=hi
            total=sum(share[c] for c in win[1:-1])
            assert total>=r.get('min_lower',0)
            if 'per' in r:assert {str(i):share[c] for i,c in enumerate(win[1:-1],1)}==r['per']
            # Independent exact loss check for this selected set, not requiring a single path.
            assert sum(share.values())+sum((12*empty[q])%deg[q] if deg[q] else 12*empty[q] for q in range(512))==12*sum(empty.values())
            checked+=1
    results=json.loads((HERE/'data/packing-results.json').read_text())
    bank=json.loads((ROOT/'work/bank9.json').read_text())
    losses=[]
    for row in bank:
        path=row['vertex_sequence'];S=set(path)
        assert len(S)==len(path)==192
        for i,x in enumerate(path):
            assert {x^(1<<a) for a in range(9)}&S==set(path[max(0,i-1):i]+path[i+1:i+2])
        deg,empty,alpha,share=statistics(S)
        E=sum(empty.values()); T=sum(alpha.values())
        assert E%4==0 and 2*E+4*T+144*len(S)==36864+4*(len(S)-2)
        loss=sum((12*empty[q])%deg[q] if deg[q] else 12*empty[q] for q in range(512))
        assert sum(share.values())+loss==12*E
        assert sum(24*alpha[x]+share[x] for x in S)+840*len(S)<=221136
        losses.append(loss)
    certified=0
    for r in results['cycles']:
        if 'weights' not in r:continue
        n=r['period'];w=list(map(F,r['weights']));b=r['bounds']
        assert all(x>=0 for x in w)
        for v in range(n):assert sum(w[i] for i in range(n) if (v-i)%n<5)<=1
        assert sum(x*y for x,y in zip(w,b))==F(r['packed'])
        assert F(r['uniform'])==F(sum(b),5)<=F(r['packed'])
        certified+=1
    log=(HERE/'logs/share-packing.log').read_text()
    names=['share_loss_identity','weighted_window_packing','five_window_dp_sound','eleven_cycle_packing','upper230_of_charge','upper231_of_charge']
    assert 'sorryAx' not in log and 'error:' not in log
    assert all(f"EmptySquarePacking.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log for name in names)
    out=dict(status='PASSED',source_files=len(manifest['files']),local_witnesses=checked,
        local_witness_note='The pinned five-window records omit vertex assignments; no local UNSAT replay is claimed.',
        bank_snakes_checked=len(bank),bank_integer_loss_M12=dict(min=min(losses),max=max(losses),total=sum(losses)),
        exact_packing_certificates=certified,lean_theorems=len(names),dp_exhaustive_controls=results['controls'],
        new_global_bound=False)
    out['maintained_sha256_lf']={str(p.relative_to(HERE)):hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
        for directory in ['lean','scripts'] for p in sorted((HERE/directory).glob('*')) if p.is_file()}
    (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
