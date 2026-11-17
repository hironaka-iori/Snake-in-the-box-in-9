from pathlib import Path
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/run_audit.py').read_text().replace('forest-search.lock','audit-search.lock')
s=s.replace("(H/'data'/(tag+'.json'))","(H/'data/exchange-audit.json')")
(H/'scripts/run_audit_verified.py').write_text(s,encoding='utf-8')
