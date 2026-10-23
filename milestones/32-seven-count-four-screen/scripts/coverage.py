"""Generate a Lean check that the 34 cases cover normalized induced windows."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
for d in ['lean','logs','upstream']:(HERE/d).mkdir(exist_ok=True)
p=ROOT/'work/spectral/stronger/WindowAutomatonDefs.lean';raw=p.read_bytes()
(HERE/'upstream/WindowAutomatonDefs.lean').write_bytes(raw)
(HERE/'data/upstream.json').write_text(json.dumps(dict(path=str(p.relative_to(ROOT)).replace('\\','/'),sha256_lf=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest()),indent=2)+'\n')
shapes=json.loads((HERE/'data/six/shapes.json').read_text())
src='''import WindowAutomatonDefs
namespace Snake9.FourRun
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def verticesFrom : Nat → List Nat → List Nat
  | v, [] => [v]
  | v, a :: ds => v :: verticesFrom (v ^^^ (1 <<< a)) ds

def induced (ds : List Nat) : Bool :=
  let vs := verticesFrom 0 ds
  decide vs.Nodup && (List.range vs.length).all (fun i =>
    (List.range vs.length).all (fun j =>
      if i+2 ≤ j then !(List.range 9).any (fun a =>
        vs.getD j 0 == (vs.getD i 0 ^^^ (1 <<< a))) else true))

def patterns : List (List Nat) := '''+repr(shapes)+'''

def covered (ds : List Nat) : Bool := !induced ds || decide (ds ∈ patterns)

theorem coverage_table : allRGS 7 0 covered = true := by decide +kernel

/-- Finite coverage; normalization and geometric exclusion are separate
obligations. This statement does not yet exclude count-four runs in snakes. -/
theorem classified (ds : List Nat) (hn : ds.length = 7)
    (hc : isRGS ds 0 = true) (hi : induced ds = true) : ds ∈ patterns := by
  have h := allRGS_spec 7 0 covered coverage_table ds hn hc
  have he : decide (ds ∈ patterns) = true := by simpa [covered,hi] using h
  exact of_decide_eq_true he

theorem patterns_valid : patterns.all (fun ds =>
    isRGS ds 0 && induced ds && ds.length == 7) = true := by decide +kernel

#print axioms coverage_table
#print axioms classified
#print axioms patterns_valid
end Snake9.FourRun
'''
(HERE/'lean/FamilyCoverage.lean').write_text(src,encoding='utf-8')
