"""Relax critical count caps to find general necessary local restrictions."""
from pathlib import Path
import importlib.util, itertools, json
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
(HERE/'data').mkdir(parents=True,exist_ok=True)
spec=importlib.util.spec_from_file_location('earlier_probe',ROOT/'milestones/40-intervening-counts/scripts/probe.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE
rows=json.loads((ROOT/'milestones/42-six-count-state-model/data/analysis.json').read_text())['cycle']
def main():
    results=[]
    for phase in [9,0,1,2,3,4,5,6,7,8,10]:
        p.DIRS=rows[phase]['directions']
        caps=rows[phase]['counts'].copy()
        for j in sorted(range(7),key=lambda j:-caps[j]):
            trial=caps.copy();trial[j]=21
            out=p.solve(f'phase-{phase}-omit-{j+1}',trial,seconds=2)
            if out['status']=='UNSAT':caps=trial
        positions=[j+1 for j,x in enumerate(caps) if x<21]
        results.append(dict(phase=phase,directions=p.DIRS,caps=caps,positions=positions))
        (HERE/'data/minimal-caps.json').write_text(json.dumps(results,indent=2)+'\n')
        print('RETAINED',phase,caps,flush=True)
if __name__=='__main__':main()
