"""Check the retained 9,9,10 projection profiles by separate SAT enumeration."""
import argparse
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_colour_three_axis import capacity_table, colour_formula, interface_table, unary_exact
from q9_three_tight_pairs import BONDS, PAIRS, SIDES, canonical, low_vertices, other, projection_banks


def run(input_path, selection, capacities, interfaces):
    saved = json.loads(selection.read_text())
    counts = tuple(saved['counts'])
    end = sum((count%2)<<i for i,count in enumerate(counts))
    f,es,cs,cross = colour_formula(counts,end,capacity_table(capacities),interface_table(interfaces))
    pool = IDPool(start_from=f.nv+1)
    def require(guard,inputs,n):
        for clause in CardEnc.equals(inputs,n,vpool=pool,encoding=EncType.cardnetwrk).clauses:
            f.append([-guard,*clause])
    for (a,b),bank in zip(PAIRS,projection_banks(counts)):
        step = 1<<other(a,b)
        loci = low_vertices(a,b)
        selectors = []
        for edges,components,crossings in bank:
            g = pool.id()
            selectors.append(g)
            for u,e,c in zip(loci,edges,components):
                links = cross[u,u|step]
                require(g,es[u]+es[u|step]+links,e)
                require(g,cs[u]+cs[u|step]+[-x for x in links],c+len(links))
            for (i,j),n in zip(SIDES,crossings):
                u,v = loci[i],loci[j]
                require(g,cross[u,v]+cross[u|step,v|step],n)
        f.append(selectors)

    rows = json.loads(input_path.read_text())['representatives']
    expected = {tuple(tuple(x) for x in rows[i])
                for i in saved['colour_survivors']}
    banks = es,cs,[cross[k] for k in BONDS]
    seen = set()
    labelled = 0
    with Cadical195(bootstrap_with=f) as s:
        while s.solve():
            m = set(s.get_model())
            key = tuple(tuple(sum(bit in m for bit in unary) for unary in bank) for bank in banks)
            normal = canonical(key,counts)
            assert normal in expected, normal
            seen.add(normal)
            labelled += 1
            s.add_clause([-lit for bank,values in zip(banks,key)
                          for bits,n in zip(bank,values) for lit in unary_exact(bits,n)])
            if labelled%50==0:
                print(json.dumps(dict(status='ENUMERATING',labelled=labelled,orbits=len(seen))),flush=True)
    assert seen==expected
    print(json.dumps(dict(status='VERIFIED',labelled=labelled,orbits=len(seen))),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('profiles',type=Path)
    p.add_argument('selection',type=Path)
    p.add_argument('caps',type=Path)
    p.add_argument('interfaces',type=Path)
    a = p.parse_args()
    run(a.profiles,a.selection,a.caps,a.interfaces)

