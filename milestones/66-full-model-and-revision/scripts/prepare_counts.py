from pathlib import Path
import itertools,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
(HERE/'lean').mkdir(exist_ok=True)
probe=json.loads((HERE/'data/replacement-cycle-probe.json').read_text())
NB=[{v^(1<<d) for d in range(9)} for v in range(512)];records=[]
for phase in probe['excluded_phases']:
    row=probe['phases'][phase];assert len(row['realizations'])==1
    r=row['realizations'][0];ds=r['directions'];j=r['violations'][0]+5;W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    T=set(W);free=set(range(9))-{ds[j-1],ds[j]}
    corners={W[j]^(1<<a)^(1<<b) for a,b in itertools.combinations(free,2)}
    forced=[q for q in sorted(corners) if any(len(NB[v]&(T|{q}))>2 for v in T|{q})]
    assert len(forced)>=3;D=forced[:3];bounds=[(0,21)]*10;bounds[j-1]=(0,2)
    name=f'CountPhase{phase:02d}';v=W[j];a,b=ds[j-1:j+1]
    src=f'''import CountChoice
namespace Snake9.LocalWindow.CountPropagation65.{name}
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := {W}
def dirs : List Nat := {ds}
def D : List Nat := {D}
def c : Centre := ⟨{v},{a},{b},0,2⟩
def bounds : List (Nat × Nat) := {bounds}
theorem canonical : Canon W dirs := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheckPlus W D=true := by decide +kernel
theorem three_corners : 3≤cnt (fun x => D.contains x) (corners c) := by decide +kernel
theorem local_lower (S : Nat → Bool) (hW : ∀ v∈W, S v=true)
    (hd : ∀ v, S v=true → cnt S (nbrs v)≤2) :
    3≤absentCorners S {v} {a} {b} := by
  have ha := forced_absent_plus S W D hW hd forced
  have hm := known_absent_count S D (corners c) ha
  rw [corners_count] at hm
  exact three_corners.trans hm
theorem in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+11≤m) (hP : ∀ j, j<dirs.length → P.fwd (dir p (r+j))=dirs.getD j 0) :
    3≤coreAlpha p (r+{j}) := by
  by_contra hn
  have hs : coreAlpha p (r+{j})≤2 := by omega
  have hb : ∀ i, i<bounds.length → (bounds.getD i (0,21)).1≤coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1)≤(bounds.getD i (0,21)).2 := by
    intro i hi
    have hi' : i<10 := by simpa [bounds] using hi
    by_cases hj : i={j-1}
    · subst i
      simpa [bounds,Nat.add_assoc] using And.intro (Nat.zero_le (coreAlpha p (r+{j}))) hs
    · have he : bounds.getD i (0,21)=(0,21) := by
        interval_cases i <;> simp_all [bounds]
      rw [he]
      exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩
  have ax := frame_axioms p P r canonical (by decide) (by simpa [dirs] using hr) hP hb
  have hc : c∈centresOf W bounds := by
    rw [centresOf_canon canonical (by decide)]
    decide +kernel
  have ha := (ax.alpha c hc).2
  have hl := local_lower _ ax.window_sel ax.deg_le_two
  change absentCorners _ {v} {a} {b}≤2 at ha
  omega
#print axioms canonical
#print axioms forced
#print axioms three_corners
#print axioms local_lower
#print axioms in_snake
end Snake9.LocalWindow.CountPropagation65.{name}
'''
    (HERE/f'lean/{name}.lean').write_text(src,encoding='utf-8')
    records.append(dict(phase=phase,directions=ds,position=j,vertex=v,forced_corners=D))
(HERE/'data/new-count-certificates.json').write_text(json.dumps(records,indent=2)+'\n')
replay=(ROOT/'milestones/65-count-saturation-share/scripts/replay.py').read_text()
replay=replay.replace("[('64-neighbour-choice-share','latest')", "[('65-count-saturation-share','latest'),('64-neighbour-choice-share','latest')")
(HERE/'scripts/replay.py').write_text(replay)
print(records)
