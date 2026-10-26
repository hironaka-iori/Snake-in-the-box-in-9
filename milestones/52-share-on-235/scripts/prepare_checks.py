"""Reuse the independent semantic-assignment test with the new formula and control."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];PRIOR=HERE.parent/'51-exact-bucket-pressure'
s=(PRIOR/'scripts/assignment_controls.py').read_text().replace('share3_47','supported0_95')
s=s.replace("HERE/'pass6/data/queries/w003-plain.json'","ROOT/'milestones/51-exact-bucket-pressure/pass2/data/queries/w018-plain.json'")
(HERE/'scripts/assignment_controls.py').write_text(s)
(HERE/'scripts/archive.py').write_text((PRIOR/'scripts/archive.py').read_text())
s=(PRIOR/'scripts/verify_geometry.py').read_text().split('positive=[];',1)[0]
(HERE/'scripts/geometry_helpers.py').write_text(s)
