from pathlib import Path
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/run_survey.py').read_text(encoding='utf-8').replace('survey.py','hamilton.py')
s=s.replace("R/'milestones/203-block-symmetry/data/bank9-input.json'","H/'data/colour-survey.json'")
(H/'scripts/run_hamilton.py').write_text(s,encoding='utf-8')
print('HAMILTON_RUNNER_PREPARED')
