"""Test count-one windows on the current critical cycle without endpoint assumptions."""
from pathlib import Path
import importlib.util,json
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
(HERE/'data').mkdir(parents=True,exist_ok=True)
spec=importlib.util.spec_from_file_location('baseprobe',ROOT/'milestones/40-intervening-counts/scripts/probe.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE
rows=json.loads((ROOT/'milestones/44-critical-window-generalization/data/analysis.json').read_text())['cycle']

def main():
    for phase,row in enumerate(rows):
        if 1 not in row['counts']:continue
        p.DIRS=row['directions'];position=row['counts'].index(1)
        caps=[21]*7;caps[position]=1
        out=p.solve(f'phase-{phase}-singleton-only',caps,seconds=3)
        if out['status']=='UNSAT':continue
        caps=[v if v<6 else 21 for v in row['counts']]
        out=p.solve(f'phase-{phase}-critical-caps',caps,seconds=4)
        if out['status']!='UNSAT':continue
        for j in sorted(range(7),key=lambda j:-caps[j]):
            if j==position or caps[j]==21:continue
            trial=caps.copy();trial[j]=21
            out=p.solve(f'phase-{phase}-omit-{j+1}',trial,seconds=2)
            if out['status']=='UNSAT':caps=trial
        print('RETAINED',phase,caps,flush=True)
        (HERE/f'data/phase-{phase}-retained.json').write_text(json.dumps(dict(phase=phase,directions=p.DIRS,caps=caps,singleton_position=position+1),indent=2)+'\n')
if __name__=='__main__':main()
