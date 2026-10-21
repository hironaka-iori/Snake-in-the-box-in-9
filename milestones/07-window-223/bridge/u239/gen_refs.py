"""Write D239Refs.lean (every range tuple of D239Table is refuted) and UpperBound239.lean."""
import json, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen import REUSE, modname
cs = [dict(c, case=c['tag']) for c in json.load(open(os.path.join(HERE, 'cases.json')))]
SYM = {c['tag'] for c in cs if c['kind'] == 'sym'}
SH = [('012', [0, 1, 2], 'P2'), ('0120', [0, 1, 2, 0], 'P3 0'), ('0123', [0, 1, 2, 3], 'P3 3'),
      ('01203', [0, 1, 2, 0, 3], 'P4 0 3'), ('01230', [0, 1, 2, 3, 0], 'P4 3 0'),
      ('01234', [0, 1, 2, 3, 4], 'P4 3 4')]
REUSEMOD = {'W2423B': 'W2423BG1Check', 'W2423C': 'W2423CG1Check', 'W224Rep': 'W224RepG1Check',
            'W232Rep': 'W232RepG1Check', 'W323Rep': 'W323RepG1Check', 'W224Dis': 'W224DisG1Check',
            'W232Dis': 'W232DisG1Check', 'W323Dis': 'W323DisG1Check'}
U = '''import D239Shape
import D239Refs
import AggregateDirectionConditional
import UpperBound241
/-!
# No flagged direction window occurs in a snake of `Q_9`; hence every snake has at most 239 edges

`upper_239_of_direction_windows` (AggregateDirectionConditional) assumes that no window of two,
three or four consecutive internal vertices has a direction shape and lumped counts flagged in
the automaton table `forbMask` (`wforb`).  `D239Shape.no_w2/3/4` discharge these premises: shape
case split and cube normalisation (forwards or backwards), the kernel-decided link from the table
to the 145 certified range tuples (`D239Table`), and their refutations (`D239Refs`).
-/
namespace Snake9

/-- **Unconditional bound**: every snake in the 9-cube has at most 239 edges. -/
theorem upper_bound_239 {m : Nat} (p : Snake m) : m ≤ 239 :=
  upper_239_of_direction_windows p (fun j hj => D239.no_w2 D239.ref_012 D239.tab_012 p j hj)
    (fun j hj => D239.no_w3 D239.ref_0120 D239.ref_0123 D239.tab_0120 D239.tab_0123 p j hj)
    (fun j hj => D239.no_w4 D239.ref_01203 D239.ref_01230 D239.ref_01234 D239.tab_01203
      D239.tab_01230 D239.tab_01234 D239.tab_01231 p j hj)

theorem upper_bound_239' : ∀ m, Nonempty (Snake m) → m ≤ 239 :=
  fun _ ⟨p⟩ => upper_bound_239 p

/-- The verified interval: a 191-edge snake exists, and no snake has more than 239 edges. -/
theorem verified_interval_191_239 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 239 :=
  ⟨lower_bound, upper_bound_239'⟩

end Snake9

#print axioms Snake9.upper_bound_239
#print axioms Snake9.verified_interval_191_239
'''


def write(out):
    imps = ['D239Table', 'UpperBound242'] + sorted(set(REUSEMOD.values()))
    imps += [modname(c['case']) + 'G1Check' for c in cs if c['case'] not in REUSE]
    s = ''.join(f'import {m}\n' for m in imps)
    s += '/-!\n# Every certified direction window of the 239 automaton is refuted\n\n'
    s += '`ref_<shape>`: each range tuple of the list `L<shape>` of `D239Table` is a packaged, kernel-checked\n'
    s += 'refutation (`Refuted2/3/4`: G2 RUP replay and G1 clause check).  Ten windows reuse the CNFs\n'
    s += 'refuted for the 241 bound (identical sha256); the 55 most expensive ones are refuted in their\nsymmetry-broken form (`RefutedL`, lex-leader clauses for the free coordinates).\n-/\nnamespace D239\nopen WinG1\n'
    for sh, d, P in SH:
        ent = [c['case'] for c in cs if c['dirs'] == d]
        term = 'forall_nil'
        for t in reversed(ent):
            r = REUSE.get(t)
            if r:
                name = '(Or.inl ' + ('WinG1.' + r if r.startswith('ref') else r + '.refuted') + ')'
            elif t in SYM:
                name = f'(Or.inr {modname(t)}.refutedL)'
            else:
                name = f'(Or.inl {modname(t)}.refuted)'
            term = f'forall_cons {name}\n    ({term})'
        s += f'theorem ref_{sh} : ∀ x ∈ L{sh}, {P} x :=\n  {term}\n'
    s += 'end D239\n'
    open(out + '/D239Refs.lean', 'w').write(s)
    open(out + '/UpperBound239.lean', 'w').write(U)


if __name__ == '__main__':
    write(sys.argv[1])
