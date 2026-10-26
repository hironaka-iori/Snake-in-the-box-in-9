"""Adapt the independent assignment controls to both selected obstruction windows."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];PRIOR=HERE.parent/'52-share-on-235'
s=(PRIOR/'scripts/assignment_controls.py').read_text()
s=s.replace("prefix=HERE/'certificates/supported0_95';meta=json.loads((HERE/'data/supported0_95.json').read_text())","prefix=HERE/f'certificates/obstruction{ROW}_95';meta=json.loads((HERE/f'data/obstruction{ROW}_95.json').read_text())")
s=s.replace("ROOT/'milestones/51-exact-bucket-pressure/pass2/data/queries/w018-plain.json'","HERE/f'data/controls/w{ROW:02d}.json'")
s=s.replace("HERE/'data/assignment-controls.json'","HERE/f'data/assignment-controls{ROW}.json'")
s=s.replace("if __name__=='__main__':main()","if __name__=='__main__':\n    import argparse\n    ap=argparse.ArgumentParser();ap.add_argument('--row',type=int,choices=[6],required=True);ROW=ap.parse_args().row\n    main()")
(HERE/'scripts/assignment_controls.py').write_text(s)
(HERE/'scripts/archive.py').write_text((PRIOR/'scripts/archive.py').read_text())
