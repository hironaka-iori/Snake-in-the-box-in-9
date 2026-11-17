from pathlib import Path
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/run_joint.py').read_text().replace('joint_search.py','degree_search.py')
(H/'scripts/run_degree.py').write_text(s,encoding='utf-8')
