from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/221-square-parity'
s=(P/'scripts/run_first.py').read_text(encoding='utf-8')
s=s.replace("H=Path(__file__).resolve().parents[1];R=H.parents[1]","H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/221-square-parity'")
s=s.replace('first_step.py','prefix_search.py').replace('first-','prefix-')
s=s.replace("H/'data/long-0/model.json',H/'data/long-78/model.json'","P/'data/long-0/model.json',P/'data/long-78/model.json',P/'data/first-summary.json',P/'data/first-audit.json'")
(H/'scripts/run_prefix.py').write_text(s,encoding='utf-8',newline='\n')
print('PREFIX_LAUNCHER_PREPARED')
