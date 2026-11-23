"""Rebuild and replay three-axis impossibility certificates before exporting cuts."""
import argparse
import json
import subprocess
from pathlib import Path

from pysat.formula import CNF

from q9_lift_three_tight_pairs import ROOT
from q9_three_axis_profiles import formula


def replay(path, checker):
    def load(name):
        return json.loads((ROOT/name).read_text())
    exact = load('verified_exact_interface_cuts_full.json')
    stars = load('verified_q6_star_cuts_first13.json')
    stars += load('verified_q6_general_star_first3.json')
    stars += load('q9_three_tight_residual.json')['cuts']
    stars = [json.loads(x) for x in sorted({json.dumps(k) for k in stars})]
    confirmed = []
    for line in path.read_text().splitlines():
        row = json.loads(line)
        if row['status']!='UNSAT_DRAT_verified':
            continue
        counts = row['counts']
        end = sum((k%2)<<i for i,k in enumerate(counts))
        assert end==row['end'] and sum(counts)<=32 and counts[0]+counts[1]>=17
        proof = Path(row['proof'])
        cnf = proof.with_suffix('.cnf')
        expected,*_ = formula(counts,end,exact,stars)
        assert expected.clauses==CNF(from_file=str(cnf)).clauses
        result = subprocess.run([checker,str(cnf),str(proof)],capture_output=True,check=True)
        assert b's VERIFIED' in result.stdout
        confirmed.append(counts)
        print(json.dumps(dict(status='PROFILE_IMPOSSIBLE_VERIFIED',counts=counts,
                              proof=str(proof))),flush=True)
    return confirmed


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('log',type=Path)
    p.add_argument('checker')
    p.add_argument('output',type=Path)
    args = p.parse_args()
    profiles = replay(args.log,args.checker)
    args.output.write_text(json.dumps(profiles)+'\n')

