"""Bounded source comparison and cofactor review; no solver or compiler."""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import re
import time

base = Path(__file__).resolve().parents[1]
start = time.perf_counter()
source = base / 'data/five-count-audit.json'
data = json.loads(source.read_bytes())
errors = []
groups = {}
sources = []
cases = 0


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


for row in data['metric_classes']:
    n = row['index']
    matrix, adj, det = row['matrix'], row['adjugate'], row['determinant']
    if det <= 0:
        errors.append([n, 'nonpositive determinant'])
        continue
    if any(sum(adj[i][k] * matrix[k][j] for k in range(5)) !=
           (det if i == j else 0) for i in range(5) for j in range(5)):
        errors.append([n, 'adjugate identity'])
    divisor = det // math.gcd(det, 315)
    forced = sum(divisor > sum(map(abs, a)) for a in adj)
    groups.setdefault(forced, []).append(n)
    if forced not in (0, 4, 5):
        errors.append([n, 'unexpected cofactor group'])
    if forced == 0:
        for rhs in product((-1, 0, 1), repeat=5):
            cases += 1
            if all(sum(a * s for a, s in zip(r, rhs)) % divisor == 0
                   for r in adj) and any(rhs):
                errors.append([n, 'nonzero admissible ternary vector', rhs])

    path = base / 'lean' / f'FiveMatrix240_{n:03d}.lean'
    text = path.read_text(encoding='utf-8')
    sources.append({'index': n, 'path': str(path), 'sha256': sha256(path)})
    declaration = (f'theorem zero_solution_{n:03d} '
                   '(x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : Int)')
    if declaration not in text:
        errors.append([n, 'integer declaration'])
    for i in range(5):
        hypothesis = f'(hs{i} : -1 \u2264 s{i} \u2227 s{i} \u2264 1)'
        quantified = f'\u2200 s{i} \u2208 ([-1,0,1] : List Int),'
        if hypothesis not in text or quantified not in text:
            errors.append([n, 'ternary range', i])
        match = re.search(r'\(h' + str(i) + r' : (.*?) = 315\*s' + str(i) + r'\)', text)
        got = re.findall(r'\((-?\d+)\)\*x(\d)', match[1]) if match else []
        if got != [(str(matrix[i][j]), str(j)) for j in range(5)]:
            errors.append([n, 'matrix equation', i])
        match = re.search(r'private theorem row_' + str(i) + r'.*? : (-?\d+)\*x' +
                          str(i) + r' = (.*?) := by omega', text)
        expected = ' + '.join(
            f'({adj[i][j]})*(' + ' + '.join(f'({matrix[j][k]})*x{k}'
                                          for k in range(5)) + ')'
            for j in range(5))
        if not match or int(match[1]) != det or match[2] != expected:
            errors.append([n, 'adjugate source identity', i])
    divisibilities = re.findall(r'\((-?\d+) \u2223 \((.*?)\)\) \u2192', text)
    if len(divisibilities) != 5:
        errors.append([n, 'divisibility count'])
    for i, (d, expression) in enumerate(divisibilities):
        got = re.findall(r'\((-?\d+)\)\*\(315\*s(\d)\)', expression)
        if int(d) != det or got != [(str(adj[i][j]), str(j)) for j in range(5)]:
            errors.append([n, 'divisibility source', i])
    conclusion = ': ' + ' \u2227 '.join(f'x{i} = 0' for i in range(5)) + ' := by'
    if conclusion not in text:
        errors.append([n, 'zero conclusion'])
    if any(marker in text for marker in ('axiom ', 'sorry', 'native_decide')):
        errors.append([n, 'unwanted source marker'])

result = {
    'status': 'PASS_SOURCE_AND_COFACTOR_REVIEW' if not errors else 'FAIL_SOURCE_AND_COFACTOR_REVIEW',
    'scope': 'Literal matrix statements, adjugate identities, ternary hypotheses, and cofactor partition. Independent 8019-case evaluation for the 33 matrices outside the strict row-sum argument.',
    'matrix_count': len(data['metric_classes']),
    'cofactor_groups': {str(k): {'count': len(v), 'indices': v} for k, v in sorted(groups.items())},
    'independent_residual_rhs_cases': cases,
    'minimum_determinant': min(r['determinant'] for r in data['metric_classes']),
    'maximum_determinant': max(r['determinant'] for r in data['metric_classes']),
    'errors': errors,
    'dataset': {'path': str(source), 'sha256': sha256(source)},
    'scripts_read': [
        {'path': str(base / 'scripts' / name), 'sha256': sha256(base / 'scripts' / name)}
        for name in ('audit_five.py', 'make_five_proofs.py', 'independent_geometry.py')],
    'generated_sources': sources,
    'review_script_sha256': sha256(Path(__file__)),
    'seconds': time.perf_counter() - start,
    'limitations': ['No compiler or solver execution', 'No rerun of the geometric enumeration',
                    'No whole-cube Lean theorem assembly', 'Source comparison is separate from kernel acceptance']
}
output = base / 'logs/five-source-review.json'
output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: result[k] for k in ('status', 'matrix_count',
                                       'independent_residual_rhs_cases', 'errors', 'seconds')}, indent=2))
