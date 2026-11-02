"""Pin the exact history dictionaries and generate their small Lean data module."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sources=[ROOT/'milestones/67-critical-family-charge/data/full-model.json',ROOT/'milestones/70-proof-supported-share-model/data/enriched-model.json',ROOT/'milestones/70-proof-supported-share-model/scripts/build.py',ROOT/'milestones/74-graph-interpretation-audit/README.md']
a,b=[json.loads(p.read_text(encoding='utf-8-sig')) for p in sources[:2]]
assert a['prefixes']==b['prefixes'] and a['patterns']==b['patterns']
prefixes=a['prefixes'];signatures=[p['signature'] for p in a['patterns']]
assert len(prefixes)==75 and prefixes[0]==[]
assert len(set(map(tuple,prefixes)))==75
assert [sum(len(p)==n for p in prefixes) for n in range(3)]==[1,31,43]
assert all(p[:-1] in prefixes for p in prefixes)
assert all(len(s)==3 and s[:-1] in prefixes for s in signatures)
for d in ['lean','data','logs','build']:(HERE/d).mkdir(exist_ok=True)
fmt=lambda rows:'[\n  '+',\n  '.join(str(r) for r in rows)+'\n]'
text='''import HistoryPrefix
import Mathlib.Data.List.Nodup
namespace Snake9.History75
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
def prefixes : List (List Nat) := '''+fmt(prefixes)+'''
def signatures : List (List Nat) := '''+fmt(signatures)+'''

theorem prefixes_empty : ([] : List Nat) ∈ prefixes := by decide
theorem prefixes_length : prefixes.length = 75 := by decide
theorem prefixes_nodup : prefixes.Nodup := by decide
theorem prefixes_closed : PrefixClosed prefixes := by unfold PrefixClosed; decide
theorem prefixes_le_two : ∀ p ∈ prefixes, p.length ≤ 2 := by decide
theorem signatures_valid : ∀ s ∈ signatures, s.length = 3 ∧ s.dropLast ∈ prefixes := by decide

theorem prefix_index_unique (i j : Fin prefixes.length)
    (h : prefixes.get i = prefixes.get j) : i = j :=
  prefixes_nodup.get_inj_iff.mp h

theorem exact_history_invariant (w : List Nat) :
    IsLongest prefixes w (run prefixes w) :=
  run_is_longest prefixes_empty prefixes_closed w

theorem exact_history_update (w : List Nat) (a : Nat) :
    longest prefixes (longest prefixes w ++ [a]) = longest prefixes (w ++ [a]) :=
  longest_update_eq prefixes_empty prefixes_closed w a

theorem exact_signature_sound (w : List Nat) (a : Nat) (sig : List Nat)
    (hsig : sig ∈ signatures) (hemit : sig <:+ run prefixes w ++ [a]) :
    sig = (w ++ [a]).drop ((w ++ [a]).length - 3) :=
  emitted_three_is_last_three prefixes_empty prefixes_closed w a sig
    (signatures_valid sig hsig).1 hemit

theorem exact_no_early_emission (w : List Nat) (a : Nat) (hshort : w.length < 2)
    (sig : List Nat) (hsig : sig ∈ signatures) :
    ¬ sig <:+ run prefixes w ++ [a] :=
  no_emission_first_two prefixes_empty prefixes_closed w a hshort sig
    (signatures_valid sig hsig).1

#print axioms prefixes_empty
#print axioms prefixes_length
#print axioms prefixes_nodup
#print axioms prefixes_closed
#print axioms prefixes_le_two
#print axioms signatures_valid
#print axioms prefix_index_unique
#print axioms exact_history_invariant
#print axioms exact_history_update
#print axioms exact_signature_sound
#print axioms exact_no_early_emission
end Snake9.History75
'''
(HERE/'lean/ExactHistory.lean').write_text(text,encoding='utf-8',newline='\n')
data=dict(status='DATA_PINNED_NOT_A_PROOF',sources=[dict(path=str(p),sha256=sha(p)) for p in sources],prefixes=prefixes,signatures=signatures,counts_by_length=[1,31,43],source_sha256=sha(HERE/'lean/ExactHistory.lean'))
(HERE/'data/source-provenance.json').write_text(json.dumps(data,indent=2)+'\n')
print('Pinned 75 prefixes and 58 signatures; generated ExactHistory.lean.')
