"""Write D239Table.lean: the certified range lists per window shape and the kernel-decided
link between the automaton table `forbMask` (WindowAutomatonData) and these lists."""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
# cases.json: the 145 cases of milestones/10-window-aggregate/data/direction_certificates.json, same order
cs = json.load(open(os.path.join(HERE, 'cases.json')))
SH = [('L012', [0, 1, 2]), ('L0120', [0, 1, 2, 0]), ('L0123', [0, 1, 2, 3]),
      ('L01203', [0, 1, 2, 0, 3]), ('L01230', [0, 1, 2, 3, 0]), ('L01234', [0, 1, 2, 3, 4])]
def write(out):
    s = 'import D239Defs\n/-!\n# The 145 certified direction windows of the 239 automaton, by shape\n\n'
    s += 'Range lists from `milestones/10-window-aggregate/data/direction_certificates.json` (one entry\n'
    s += 'per certificate; `(6, 21)` is the lumped count `>= 6`).  `tab_*`: every window flagged in\n'
    s += '`forbMask` (`wforb1`, the predicate of `upper_239_of_direction_windows`) with symbols `0..6`\n'
    s += 'is covered by an entry of the list of its shape (kernel decision); the shape `01231` is never\n'
    s += 'flagged.\n-/\nnamespace D239\nopen Snake9.WindowAutomaton\n'
    for name, d in SH:
        ent = [c['alpha'] for c in cs if c['dirs'] == d]
        s += f'/-- shape {"".join(map(str, d))}: {len(ent)} windows -/\n'
        s += f'def {name} : List (List (Nat × Nat)) := [' + ',\n  '.join('[' + ', '.join(f'({a}, {b})' for a, b in e) + ']' for e in ent) + ']\n'
    for name, d in SH:
        k = len(d) - 1
        s += f'theorem tab_{name[1:]} : tab{k} {d} {name} = true := by decide +kernel\n'
    s += 'theorem tab_01231 : tab4 [0, 1, 2, 3, 1] [] = true := by decide +kernel\n'
    s += 'end D239\n'
    open(out + '/D239Table.lean', 'w').write(s)


if __name__ == '__main__':
    write(sys.argv[1])
