"""Reuse the completed split interpretation pipeline for two obstruction windows."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];PRIOR=HERE.parent/'52-share-on-235'
(HERE/'lean').mkdir(exist_ok=True)
s=(PRIOR/'scripts/export_share.py').read_text()
s=s.replace("NAME='supported0_95';MOD='SharePressure520';prefix=HERE/'certificates'/NAME", "import argparse\nap=argparse.ArgumentParser();ap.add_argument('--row',type=int,choices=[0,5],required=True);args=ap.parse_args()\nNAME=f'obstruction{args.row}_95';MOD=f'ShareObstruction53{args.row}';prefix=HERE/'certificates'/NAME")
s=s.replace('off=6000','off=8000').replace("HERE/'lean/SharePressure.lean'","HERE/f'lean/ShareBound{args.row}.lean'")
(HERE/'scripts/export_share.py').write_text(s)
s=(PRIOR/'scripts/lrat_share.py').read_text().replace('(2400, 3000, 4000, 5000, 6000)','(2400, 3000, 4000, 5000, 6000, 8000)').replace("6000: 'O6k'","6000: 'O6k', 8000: 'O8k'")
(HERE/'scripts/lrat_share.py').write_text(s)
for name in ['LratCheckO6k','LratFastO6k14','LratFastO6k15']:
 (HERE/f'lean/{name.replace("O6k","O8k")}.lean').write_text((PRIOR/f'lean/{name}.lean').read_text().replace('O6k','O8k').replace('6000','8000'))
s=(PRIOR/'scripts/split_semantics.py').read_text().replace("HERE=Path(__file__).resolve().parents[1];MOD='SharePressure520';NS='Snake9.LocalWindow.'+MOD", "import argparse\nap=argparse.ArgumentParser();ap.add_argument('--row',type=int,choices=[0,5],required=True);args=ap.parse_args()\nHERE=Path(__file__).resolve().parents[1];MOD=f'ShareObstruction53{args.row}';NS='Snake9.LocalWindow.'+MOD")
s=s.replace("HERE/'data/original-semantic-module.txt'","HERE/f'data/original-semantic-module{args.row}.txt'").replace("HERE/'data/supported0_95.json'","HERE/f'data/obstruction{args.row}_95.json'").replace("HERE/'certificates/supported0_95.meanings.json.gz'","HERE/f'certificates/obstruction{args.row}_95.meanings.json.gz'").replace("HERE/'certificates/supported0_95.cnf'","HERE/f'certificates/obstruction{args.row}_95.cnf'").replace('==7208',"==meta['core_clauses']").replace("HERE/'data/semantic-split.json'","HERE/f'data/semantic-split{args.row}.json'")
(HERE/'scripts/split_semantics.py').write_text(s)
s=(PRIOR/'scripts/replay.py').read_text().replace("for prior,tag in [","for prior,tag in [('52-share-on-235','latest'),")
(HERE/'scripts/replay.py').write_text(s)
for row,ds in [(0,[0,1,2,0,3,4]),(5,[0,1,2,3,4,5])]:
 names=list('abcdef')[:max(ds)+1];ls='['+','.join(names)+']';word='['+','.join(names[d] for d in ds)+']'
 ns=f'Snake9.LocalWindow.ShareObstruction53{row}'
 s=f'''import ShareFrame
import ShareBound{row}
namespace {ns}
def directions : List Nat := {ds}
theorem share_in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → P.fwd (dir p (r+j)) = directions.getD j 0)
    (hb : ∀ i, i<5 → (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) :
    96 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  exact refuted_share_bridge p P r refuted_share
    (cs := directions) ⟨rfl,rfl,by decide⟩ (by decide) hr hd hb
theorem named_share_in_snake {{m : Nat}} (p : Snake m) (r {' '.join(names)} : Nat)
    (hn : {ls}.Nodup) (h9 : ∀ x ∈ {ls}, x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ({word} : List Nat).getD j 0)
    (hb : ∀ i, i<5 → (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) :
    96 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply share_in_snake p (mkPerm {ls}) r hr ?_ hb
  intro j hj
  rw [hd j hj]
  interval_cases j
'''+''.join(f'  · exact hs {d} (by simp)\n' for d in ds)+f'#print axioms share_in_snake\n#print axioms named_share_in_snake\nend {ns}\n'
 (HERE/f'lean/ShareInSnake{row}.lean').write_text(s)
