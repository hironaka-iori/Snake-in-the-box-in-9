"""Export exact three-centre interval keys for a kernel table-coverage check.

No SAT solving or refutation claim is made by this script.
"""
import hashlib
import json
import runner as r

PIN = '75404cc705135dd1f0526ecc9f1d198d3fbf0366'
SOURCE = 'milestones/10-window-aggregate/data/minimal_L7_k6_K7_r3_r34.json'
EXPECTED = 'de9e5c0e872f3a54fc8638cb5eafb01e114357de31e746cd492fed8eb1eb9993'


def main():
    data = r.blob(PIN, SOURCE)
    assert hashlib.sha256(data).hexdigest() == EXPECTED
    records = [(i, row) for i, row in enumerate(json.loads(data)['exclusions']) if len(row['alpha']) == 3]
    assert len(records) == 91
    entries = ['(' + str(row['dirs']) + ', [' + ', '.join(f'({a},{b})' for a, b in row['alpha']) + '])'
               for _, row in records]
    code = '''import CountWindowTable231

/-! Exact three-centre keys from the frozen 231 source set. Their concrete
refutations remain an explicit premise; this file checks table coverage only. -/
namespace Snake9.CountWindowTriples231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge CountWindowTable231
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def keys : List IntervalKey := [
  ''' + ',\n  '.join(entries) + ''']

theorem table_checked : tableCovered keys 4 = true := by decide +kernel

theorem no_triple_window (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m)
    (r : Nat) (hr : r + 4 ≤ m) :
    wforbK6R34C7W (dsOf p r 4) (symsK p 8 r 4) = false :=
  no_window table_checked h p r (by decide) hr

/-- Exactly the `hw3` premise of the existing conditional 231 theorem. -/
theorem hw3_of_triples (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m) :
    ∀ r, r + 4 ≤ m → wforbK6R34C7W
      [pathDir p r, pathDir p (r+1), pathDir p (r+2), pathDir p (r+3)]
      [symK 8 (countSeq p (r+1)), symK 8 (countSeq p (r+2)), symK 8 (countSeq p (r+3))] = false := by
  intro r hr
  rw [countSeq_eq_coreAlpha p (r+1) (by omega), countSeq_eq_coreAlpha p (r+2) (by omega),
    countSeq_eq_coreAlpha p (r+3) (by omega), pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
  exact no_triple_window h p r hr

#print axioms table_checked
#print axioms no_triple_window
#print axioms hw3_of_triples
end Snake9.CountWindowTriples231
'''
    output = r.ROOT / 'work/spectral/stronger/CountWindowTriples231.lean'
    if output.exists():
        assert output.read_text(encoding='utf-8') == code, 'Existing source differs'
    else:
        output.write_text(code, encoding='utf-8', newline='\n')
    r.atomic(r.HERE / 'runtime/count-triples-table/input.json', dict(
        source_commit=PIN, source_path=SOURCE, source_sha256=EXPECTED,
        selected_indices=[i for i, _ in records], keys=len(records),
        generated_source_sha256=r.digest(output), script_sha256=r.digest(__file__),
        scope='Exact key export; neither table coverage nor local refutations asserted by Python'))
    print('Exported', len(records), 'exact keys; kernel check remains to run')


if __name__ == '__main__':
    main()
