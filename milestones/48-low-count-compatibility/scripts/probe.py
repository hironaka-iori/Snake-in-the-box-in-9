"""Test whether low-count coexistence or hidden excess excludes the new critical cycle."""
from pathlib import Path
import importlib.util,json
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
(HERE/'data').mkdir(parents=True,exist_ok=True)
spec=importlib.util.spec_from_file_location('baseprobe',ROOT/'milestones/40-intervening-counts/scripts/probe.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE
rows=json.loads((ROOT/'milestones/47-critical-singleton-patterns/data/analysis.json').read_text())['cycle']
def main():
    results=[]
    for phase in [8,0,1,2,3,9,10,4,5,6,7]:
        row=rows[phase];p.DIRS=row['directions'];caps=[v if v<6 else 21 for v in row['counts']]
        out=p.solve(f'phase-{phase}-interval',caps,seconds=4)
        if out['status']=='UNSAT':
            for j in sorted(range(7),key=lambda j:-caps[j]):
                if caps[j]==21:continue
                trial=caps.copy();trial[j]=21
                test=p.solve(f'phase-{phase}-omit-{j+1}',trial,seconds=2)
                if test['status']=='UNSAT':caps=trial
            results.append(dict(phase=phase,directions=p.DIRS,caps=caps))
        elif 6 in row['counts']:
            p.solve(f'phase-{phase}-no-excess',row['counts'],seconds=4)
        (HERE/'data/retained.json').write_text(json.dumps(results,indent=2)+'\n')
        print('RETAINED',phase,caps,flush=True)
if __name__=='__main__':main()
