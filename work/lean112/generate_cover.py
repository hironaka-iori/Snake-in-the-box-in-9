"""Generate bank-indexed statements, checking each translation inclusion in Lean."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
DEST=HERE/'bank'
def emit(entry,rep,shift):
    local='First112' if entry==0 else f'E112{entry:03d}'
    owner='First112' if rep==0 else f'E112{rep:03d}'
    imports=[local+'Data','DfsBankData','CubeLocal']
    imports+=['First112Reuse' if rep==0 else owner+'Complete']
    s=''.join('import '+m+'\n' for m in dict.fromkeys(imports))
    s+='namespace Snake9.Regrowth.Bank112\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
    s+=f'theorem prefix_match{entry} : ∀ i : Fin 112, {local}.pre[i.val]! = (Dfs.oriented {entry})[i.val]! := by decide\n'
    if entry!=rep:
        s+=f'theorem translate_region{entry} : ∀ v : Vertex, v ∈ {local}.region → vxor ({shift} : Vertex) v ∈ {owner}.region := by decide\n'
        s+=f'theorem translate_head{entry} : vxor ({shift} : Vertex) {local}.head = {owner}.head := by decide\n'
    s+=f'''theorem entry{entry} (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented {entry}) 112) : False := by
  have hp' : Dfs.StartsWith p {local}.pre 112 := by
    intro i hi hpLen
    rw [prefix_match{entry} ⟨i,hi⟩]
    exact hp i hi hpLen
'''
    if entry==rep:s+=f'  exact {owner}.no192 p hp\'\n'
    else:s+=f'''  let q := translate (suffix p) ({shift} : Vertex)
  apply {owner}.region_exclusion q
  constructor
  · change vxor ({shift} : Vertex) ((suffix p).vertex 0) = {owner}.head
    rw [{local}.suffix_head p hp',translate_head{entry}]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region{entry} _ ({local}.suffix_covered p hp' _ ⟨i,rfl⟩)
'''
    s+=f'#print axioms entry{entry}\nend Snake9.Regrowth.Bank112\n'
    name=f'Bank112Entry{entry:03d}';path=DEST/(name+'.lean')
    if not path.exists() or path.read_text(encoding='utf-8')!=s:path.write_text(s,encoding='utf-8')
    return name

def aggregate():
    s=''.join(f'import Bank112Entry{i:03d}\n' for i in range(262))
    s+='''namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem bank_no192 : ∀ j : Nat, j < 262 → ∀ p : Snake 192,
    Dfs.StartsWith p (Dfs.oriented j) 112 → False
'''
    s+=''.join(f'  | {i}, _, p, hp => entry{i} p hp\n' for i in range(262))
    s+='''  | n+262, hj, _, _ => False.elim (by omega)

theorem bank_no_long_prefix (j : Nat) (hj : j < 262) {m : Nat}
    (hm : 192 ≤ m) (p : Snake m) : ¬ Dfs.StartsWith p (Dfs.oriented j) 112 := by
  intro hp
  apply bank_no192 j hj (takePrefix p hm)
  intro i hi hiLen
  exact hp i hi (by omega)

theorem bank_no_long_suffix (j : Nat) (hj : j < 262) {m : Nat}
    (hm : 192 ≤ m) (p : Snake m) : ¬ Dfs.EndsWith p (Dfs.oriented j) 112 :=
  bank_no_long_prefix j hj hm (reverseSnake p)

theorem bank_end_segment_length_le191 (j : Nat) (hj : j < 262)
    {m : Nat} (p : Snake m)
    (h : Dfs.StartsWith p (Dfs.oriented j) 112 ∨ Dfs.EndsWith p (Dfs.oriented j) 112) : m ≤ 191 := by
  by_cases hm : 192 ≤ m
  · rcases h with h | h
    · exact False.elim (bank_no_long_prefix j hj hm p h)
    · exact False.elim (bank_no_long_suffix j hj hm p h)
  · omega

#print axioms bank_no192
#print axioms bank_no_long_prefix
#print axioms bank_no_long_suffix
#print axioms bank_end_segment_length_le191
end Snake9.Regrowth.Bank112
'''
    (DEST/'Bank112Results.lean').write_text(s,encoding='utf-8')
    return 'Bank112Results'

if __name__=='__main__':
    import sys
    i=int(sys.argv[1]);e=json.loads((ROOT/'outputs/lean112/cover.json').read_text())['entries'][str(i)]
    print(emit(i,e['representative'],e['translation']))
