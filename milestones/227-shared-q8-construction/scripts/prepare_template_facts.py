"""Emit the bounded literal Lean facts for round 227; never invoke Lean."""
from pathlib import Path
import argparse
import hashlib
import json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def nat_list(values):
    return '[' + ', '.join(str(value) for value in values) + ']'


def main(source_only=False):
    paths = {
        'regions': H / 'data/regions44.json',
        'initial': H / 'data/companions.json',
        'remaining': H / 'data/remaining-companions.json',
        'previous': R / 'milestones/226-connected-replacement-search/data/search-summary.json',
    }
    pins = {str(path): sha(path) for path in paths.values()}
    data = {name: json.loads(path.read_bytes()) for name, path in paths.items()}
    ids = sorted(set(data['previous']['width44_unresolved'])
                 - set(data['previous']['shared_q8_contexts']))
    if len(ids) != 35 or ids != [row['context'] for row in data['remaining']['contexts']]:
        raise ValueError('The intended 35-context selection has changed.')
    configurations = data['initial']['configurations']
    if len(configurations) != 18 or [row['id'] for row in configurations] != list(range(18)):
        raise ValueError('The intended 18 initial configurations have changed.')
    first_anchors = data['initial']['first_lower_anchors']
    first_edges = data['initial']['first_lower_edges']
    rows = []
    for ident in ids:
        row = data['regions']['contexts'][ident]
        if row['id'] != ident:
            raise ValueError('Context index does not match its stored identifier.')
        first, second = row['parts']
        rows.append(dict(context=ident, firstStart=first['anchors'][0],
                         firstFinish=first['anchors'][1],
                         budget=row['replacement_crossings'],
                         secondStart=second['anchors'][0],
                         secondFinish=second['anchors'][1],
                         upper=[v for v in second['allowed'] if v >= 256]))

    source = '''import Std

set_option Elab.async false
set_option maxRecDepth 4096

namespace TemplateFacts227

-- Literal extraction is pinned by the generator receipt, not proved by Lean.
-- Boolean evaluation and structural proofs are checked by the kernel.
structure ContextRow where
  context : Nat
  firstStart : Nat
  firstFinish : Nat
  budget : Nat
  secondStart : Nat
  secondFinish : Nat
  upper : List Nat

structure LowerTask where
  firstAnchors : List Nat
  firstEdges : Nat
  firstDomain : List Nat
  lowerAnchors : List Nat
  lowerEdges : Nat
  lowerDomain : List Nat

def remainingContexts : List ContextRow := [
'''
    context_literals = []
    for row in rows:
        fields = [f'{key} := {row[key]}' for key in
                  ['context', 'firstStart', 'firstFinish', 'budget', 'secondStart', 'secondFinish']]
        fields.append('upper := ' + nat_list(row['upper']))
        context_literals.append('  { ' + ', '.join(fields) + ' }')
    source += ',\n'.join(context_literals) + '\n]\n\n'
    source += '''theorem remaining_face_budgets :
    remainingContexts.length = 35 ∧
    remainingContexts.map ContextRow.context = ''' + nat_list(ids) + ''' ∧
    (remainingContexts.all (fun row => decide (
      row.firstStart < 256 ∧ row.firstFinish < 256 ∧
      row.secondStart < 512 ∧ row.secondFinish < 512 ∧
      ((row.budget = 1 ∧
        ((row.secondStart < 256 ∧ 256 ≤ row.secondFinish) ∨
         (256 ≤ row.secondStart ∧ row.secondFinish < 256))) ∨
       (row.budget = 2 ∧ 256 ≤ row.secondStart ∧ 256 ≤ row.secondFinish ∧
        row.upper.length < 45))))) = true := by
  refine ⟨rfl, rfl, ?_⟩
  decide

'''
    for row in configurations:
        fields = [
            'firstAnchors := ' + nat_list(first_anchors),
            'firstEdges := ' + str(first_edges),
            'firstDomain := ' + nat_list(row['first_domain']),
            'lowerAnchors := ' + nat_list(row['lower_anchors']),
            'lowerEdges := ' + str(row['lower_edges']),
            'lowerDomain := ' + nat_list(row['lower_domain']),
        ]
        source += 'def task' + str(row['id']) + ' : LowerTask := {\n  '
        source += ',\n  '.join(fields) + '\n}\n\n'
    source += '''theorem first_literal_class :
    ∀ task, task ∈ [task0, task2, task4, task6, task8, task10, task12] →
      task = task0 := by
  intro task membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem second_literal_class :
    ∀ task, task ∈ [task1, task3, task5, task7, task9, task11, task13] →
      task = task1 := by
  intro task membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem task17_contained_in_task0 :
    task17.firstAnchors = task0.firstAnchors ∧
    task17.firstEdges = task0.firstEdges ∧
    task17.lowerAnchors = task0.lowerAnchors ∧
    task17.lowerEdges = task0.lowerEdges ∧
    task17.firstDomain ⊆ task0.firstDomain ∧
    task17.lowerDomain ⊆ task0.lowerDomain := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have filtered : task17.firstDomain =
        task0.firstDomain.filter (fun v => v != 212) := rfl
    intro v member
    rw [filtered] at member
    exact (List.mem_filter.mp member).1
  · have filtered : task17.lowerDomain =
        task0.lowerDomain.filter (fun v => v != 212) := rfl
    intro v member
    rw [filtered] at member
    exact (List.mem_filter.mp member).1

#print axioms remaining_face_budgets
#print axioms first_literal_class
#print axioms second_literal_class
#print axioms task17_contained_in_task0
end TemplateFacts227
'''
    output = H / 'lean/TemplateFacts227.lean'
    output.parent.mkdir(exist_ok=True)
    for path, expected in pins.items():
        if sha(Path(path)) != expected:
            raise ValueError('An input changed during source generation: ' + path)
    output.write_text(source, encoding='utf-8', newline='\n')
    receipt = dict(
        status='SOURCE_PREPARED_NOT_COMPILED',
        input_pins=pins,
        generator=str(Path(__file__).resolve()),
        generator_sha256=sha(Path(__file__)),
        source=str(output), source_sha256=sha(output), source_bytes=output.stat().st_size,
        source_imports=['Std'],
        context_ids=ids, initial_configuration_ids=list(range(18)),
        equality_groups=[[0, 2, 4, 6, 8, 10, 12], [1, 3, 5, 7, 9, 11, 13]],
        domination=[17, 0],
        extraction={
            'contexts': 'regions44.contexts[id].parts anchors and replacement_crossings',
            'upper_lists': 'regions44.contexts[id].parts[1].allowed filtered by v>=256, preserving order',
            'first_anchors_and_edges': 'companions.first_lower_anchors and first_lower_edges',
            'initial_tasks': 'companions.configurations[id] first_domain, lower_anchors, lower_edges, lower_domain',
        },
        reports=['TemplateFacts227.remaining_face_budgets', 'TemplateFacts227.first_literal_class',
                 'TemplateFacts227.second_literal_class', 'TemplateFacts227.task17_contained_in_task0'],
        data_extraction_lean_checked=False, literal_facts_lean_checked=False,
        proof_method='Boolean all for face/budget facts; literal equality by membership cases '
                     'and reflexivity; domain containment through exact filtering of vertex212.',
        scope='Prepared concrete finite facts only. No compiler, solver or traversal was run. '
              'Kernel acceptance remains pending. Extraction from JSON, enumeration coverage, '
              'solver infeasibility, and the complete snake interpretation remain separate obligations.',
    )
    receipt_path = H / 'data/template-facts-source.json'
    if not source_only:
        receipt_path.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(json.dumps(dict(status=receipt['status'], source_bytes=receipt['source_bytes'],
                         source_sha256=receipt['source_sha256'], reports=len(receipt['reports']),
                         receipt_written=not source_only)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true',
                        help='Regenerate only Lean source, leaving all existing receipts unchanged.')
    main(source_only=parser.parse_args().source_only)
