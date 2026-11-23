"""Independently check path and near-path inputs, canonical classes, and repair outcomes."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

def read(path):
    return [list(map(int,l.split())) for l in Path(path).read_text().splitlines()]

def inspect(p):
    assert p and 0<=min(p)<=max(p)<512 and len(set(p))==len(p)
    collisions=[]
    for j,y in enumerate(p):
        for i,x in enumerate(p[:j]):
            edge=(x^y).bit_count()==1
            if j==i+1:assert edge
            elif edge:collisions.append((i,j))
    def relabel(t):
        keys={}
        return bytes(keys.setdefault(x,len(keys)) for x in t)
    t=[x^y for x,y in zip(p,p[1:])]
    return min(relabel(t),relabel(reversed(t))),collisions

def records(path):
    keys=set();gaps=Counter()
    for p in read(path):
        key,errors=inspect(p)
        assert len(p)==193 and len(errors)==1 and key not in keys
        keys.add(key)
        a,b=errors[0];gaps[b-a]+=1
    return keys,gaps

def main():
    old,_=records('q9_onechord_expanded_800.txt')
    fresh,gaps=records('q9_port_all_new_onechord.txt')
    reached,_=records('q9_port_all_new_plateau.txt')
    assert fresh.isdisjoint(old) and fresh<=reached
    result=dict(old=len(old),new=len(fresh),gap_counts=gaps,closure_size=len(reached),closure_outside_old=len(reached-old))
    corp=gzip.open('q9_forest_port_sources.txt.gz','rb').read()
    result.update(corpus_sha256=hashlib.sha256(corp).hexdigest(),source_rows=len(corp.splitlines()))
    ctrl=list(map(int,Path('q9_port_two_pivot_control.log').read_text().split(' vertices ')[1].split()))
    assert len(ctrl)==192 and not inspect(ctrl)[1]
    c0=read('q9_port_two_pivot_control.txt')[0]
    result.update(control_edges=len(ctrl)-1,damaged_control_chords=len(inspect(c0)[1]))
    for f in ('q9_port_free_repair.jsonl','q9_fixed_port_pattern.jsonl'):
        hist=Counter()
        for line in Path(f).read_text().splitlines():
            row=json.loads(line);status,w=row[-2:]
            if w:
                assert status=='FOUND' and len(w)>=(192 if row[0]=='control' else 193) and not inspect(w)[1]
            if row[0]!='control':hist[status]+=1
        result[f]=hist
    for f in ('q9_forest_ports_combined.log','q9_forest_ports_sparse.log','q9_forest_ports_combined_mutated.log','q9_forest_ports_dualmut.log','q9_port_full_pivot.log','q9_port_two_pivot.log','q9_port_two_pivot14.log'):
        lines=Path(f).read_text().splitlines()
        result[f]=[l for l in lines if l.startswith(('DONE','MUTATED','NEAR','FOUND','PATH'))]
    for f in ("q9_port_parity_control.log","q9_port_cross_control.log"):
        w=list(map(int,Path(f).read_text().splitlines()[0].split()[1:]))
        assert len(w)==191 and not inspect(w)[1]
    for f in ("q9_port_parity_repair.log","q9_port_reversed_parity.log","q9_port_reverse_two_drop.log","q9_port_four_same.log","q9_port_four_reversed.log","q9_port_cross_majority_all.log","q9_port_cross_minority_deep.log"):
        if Path(f).exists():result[f]=[l for l in Path(f).read_text().splitlines() if l.startswith(("DONE","FOUND"))]
    for file in sorted(Path(".").glob("q9_port_radius*.jsonl")):
        status=Counter();seen=set()
        for line in file.read_text().splitlines():
            row,r,st,domain,cuts,w=json.loads(line)
            if w:
                assert st=="FOUND" and not inspect(w)[1]
            if row=="control":assert st=="FOUND";continue
            assert row not in seen;seen.add(row);status[st]+=1
        result[file.name]=dict(checked=len(seen),status=status)
        if file.name=="q9_port_radius4_supports.jsonl":
            assert seen==set(range(260)) and status=={"UNSAT":260}
    donors=Counter()
    with gzip.open("q9_port_highdim_parents.txt.gz","rt") as src:
        for l in src:
            d,*w=map(int,l.split());S=set(w);assert len(S)==len(w) and max(S)<1<<d
            assert all((a^b).bit_count()==1 for a,b in zip(w,w[1:]))
            assert sum((x^(1<<j)) in S for x in S for j in range(d))==2*(len(S)-1)
            donors[d]+=1
    result["high_dimensional_verified_parents"]=donors
    stats=[]
    for f in ("q9_port_highdim_free_face.jsonl","q9_port_highdim_exact192.jsonl"):
        t={}
        for l in Path(f).read_text().splitlines():
            row=json.loads(l);st,w=row[-2:]
            if w:assert st=="FOUND" and not inspect(w)[1]
            if row[0]=="control":assert len(w)>=192;continue
            assert row[0] not in t;t[row[0]]=st
        stats.append(t);result[f]=Counter(t.values())
    assert set(stats[0])==set(stats[1]) and len(stats[0])==600
    result["high_dimensional_faces_excluded_at_192"]=sum(any(t[i]=="UNSAT" for t in stats) for i in stats[0])
    w=list(map(int,Path("q9_high_section_bridge_control.log").read_text().split()[1:]))
    assert len(w)>=192 and not inspect(w)[1]
    result["high_dimensional_bridges"]=Path("q9_high_section_bridge.log").read_text().strip()
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
