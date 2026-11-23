"""Reconstruct each rejected port star as a finite cardinality problem."""

import argparse
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q6_star_interfaces import check
from q9_geometry_cut_library import orientations
from q9_join_interface_masks import Catalogue, vertices


def verify(table, artifact, checker):
    catalogue = Catalogue(table)
    rows = json.loads(artifact.read_text())["patterns"]
    checked_roots = 0
    seen = set()
    for row in rows:
        assert Path(row["catalogue"]).resolve() == table.resolve()
        e, c, leaves = row["root_star"]
        keys = [(e, c, *case) for case in leaves]
        assert len(keys) in (2, 3) and all(key in catalogue.banks for key in keys)
        faces = [(0, e, c)] + [(1 << i, f, d) for i, (f, d, _) in enumerate(leaves)]
        links = [(0, 1 << i, r) for i, (_, _, r) in enumerate(leaves)]
        actual = tuple(map(tuple, row["faces"])), tuple(map(tuple, row["links"]))
        assert min(orientations(faces, links)) == actual and actual not in seen
        seen.add(actual)
        roots = set.intersection(*(set(catalogue.banks[key]) for key in keys))
        for root in roots:
            f = CNF()
            pool = IDPool()
            selected = list(vertices(root))
            incident = {v: [] for v in selected}
            for key in keys:
                selectors = []
                contacts = sorted({root & neighbor for neighbor in catalogue.banks[key][root]})
                for mask in contacts:
                    choice = pool.id()
                    selectors.append(choice)
                    for v in vertices(mask):
                        incident[v].append(choice)
                f.extend(CardEnc.equals(selectors, 1, vpool=pool, encoding=EncType.seqcounter))
            for v in selected:
                degree = sum(bool(root & (1 << (v ^ (1 << axis)))) for axis in range(6))
                f.extend(CardEnc.atmost(incident[v], 2 - degree, vpool=pool,
                                       encoding=EncType.seqcounter))
            with Cadical195(bootstrap_with=f, with_proof=True) as solver:
                assert solver.solve() is False, row["root_star"]
                proof = "\n".join(solver.get_proof() or ["0"]) + "\n"
            check(f, proof, checker)
            checked_roots += 1
    print(json.dumps(dict(status="VERIFIED", port_stars=len(seen),
                          checked_root_formulas=checked_roots)), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("table", type=Path)
    parser.add_argument("artifact", type=Path)
    parser.add_argument("checker")
    args = parser.parse_args()
    verify(args.table, args.artifact, args.checker)
