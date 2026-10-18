"""Re-enumerate every cell subset and diagnose the restrictive palette.

This is a computational census. The Lean reduction checks the finite numerical
profiles and their sum; its application to all geometric subsets still relies
on this enumeration, rather than a Lean completeness theorem.
"""
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]


def main():
    tables = json.loads((ROOT/'milestones/16-cycle-reservoirs/data/cell-states.json').read_text())['tables']
    result = {'scope':'Complete Python subset enumeration; Lean checks profile arithmetic and a conditional sum bound, not enumeration completeness.',
              'types':[]}
    profiles = set()
    for table in tables:
        vertices = table['vertices']
        graph_edges = [(i,j) for j in range(18) for i in range(j) if (vertices[i]^vertices[j]).bit_count() == 1]
        recovered = {}; acyclic = []
        for size in range(19):
            for chosen in itertools.combinations(range(18),size):
                bits = sum(1<<i for i in chosen)
                degree = [0]*18; parent = list(range(18)); has_cycle = False
                def root(i):
                    while parent[i] != i: i = parent[i]
                    return i
                for i,j in graph_edges:
                    if bits>>i&1 and bits>>j&1:
                        degree[i] += 1; degree[j] += 1
                        a,b = root(i),root(j)
                        if a == b: has_cycle = True
                        else: parent[a] = b
                if any(degree[i] not in (1,2) for i in chosen if i < 14): continue
                if any(degree[i] > 2 for i in chosen): continue
                endpoints = sum(degree[i] == 1 for i in chosen if i < 14)
                if endpoints > 2: continue
                row = [bits,bits>>14,*[degree[i] if i in chosen else 0 for i in range(14,18)],endpoints,size]
                recovered[bits] = row
                if not has_cycle:
                    acyclic.append(row); profiles.add((size,endpoints))
                    assert size <= 10+4*endpoints
        assert recovered == {r[0]:r for r in table['rows']}
        maxima = [max(r[-1] for r in acyclic if r[-2] == e) for e in range(3)]
        assert len(recovered) == 4973 and len(acyclic) == 4142 and maxima == [10,14,14]
        result['types'].append({'subsets_examined':2**18,'matched_table_rows':len(recovered),
                                'acyclic_rows':len(acyclic),'max_vertices_by_internal_endpoints':maxima})
    result['profiles'] = sorted(profiles)
    result['conditional_total_vertices'] = 16*10+4*2
    (HERE/'data/capacity-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    pairs = '['+','.join(f'({a},{b})' for a,b in sorted(profiles))+']'
    lean = '''import CycleCuts
namespace Snake9.GlobalCells.Capacity
open Finset
def profiles : List (Nat × Nat) := PROFILES
theorem profiles_checked : profiles.all (fun r => decide (r.1 ≤ 10+4*r.2)) = true := by decide
theorem profile_bound (c e : Nat) (h : (c,e) ∈ profiles) : c ≤ 10+4*e := by
  exact of_decide_eq_true (List.all_eq_true.mp profiles_checked (c,e) h)
/-- The geometric application requires the separate local census premise. -/
theorem conditional_total (c e : Fin 16 → Nat)
    (h : ∀ i, c i ≤ 10+4*e i) (he : (∑ i, e i) ≤ 2) :
    (∑ i, c i) ≤ 168 := by
  calc
    (∑ i, c i) ≤ ∑ i, (10+4*e i) := Finset.sum_le_sum (fun i _ => h i)
    _ = 160+4*(∑ i, e i) := by simp [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 168 := by omega
theorem table_total (c e : Fin 16 → Nat)
    (h : ∀ i, (c i,e i) ∈ profiles) (he : (∑ i, e i) ≤ 2) :
    (∑ i, c i) ≤ 168 :=
  conditional_total c e (fun i => profile_bound _ _ (h i)) he
#print axioms profiles_checked
#print axioms profile_bound
#print axioms conditional_total
#print axioms table_total
end Snake9.GlobalCells.Capacity
'''.replace('PROFILES',pairs)
    (HERE/'lean/Capacity.lean').write_text(lean,encoding='utf-8',newline='\n')
    print(json.dumps(result['types']))


if __name__ == '__main__': main()
