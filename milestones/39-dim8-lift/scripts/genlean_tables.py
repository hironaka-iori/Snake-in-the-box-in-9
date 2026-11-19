"""Write the cover tables and representative lists as Lean data modules (lean/gen/, not committed).
usage: python3 genlean_tables.py tablesdir chunk"""
import sys, os
tdir, chunk = sys.argv[1], int(sys.argv[2])
HERE = os.path.dirname(os.path.abspath(__file__))
G = os.path.join(HERE, '..', 'lean', 'gen'); os.makedirs(G, exist_ok=True)
D = os.path.join(HERE, '..', 'data')
hdr = "set_option maxRecDepth 100000\n"
reps = [(int(l.split()[0]), int(l.split()[2], 16)) for l in open(os.path.join(D, 'q6_29.txt'))]
q5 = [int(l.split()[2], 16) for l in open(os.path.join(D, 'q5_15.txt')) if int(l.split()[0]) >= 15]
with open(os.path.join(G, 'Reps.lean'), 'w') as f:
    f.write(hdr + "namespace Dim8Lift.Tab\n/-- the 2161 representatives (size, mask) of Q6 forests with >= 29 vertices -/\ndef reps : List (Nat × Nat) := [\n"
            + ",\n".join("(%d, %d)" % r for r in reps) + "]\n/-- the 35 representatives of Q5 forests with >= 15 vertices -/\ndef q5reps : List Nat := ["
            + ", ".join(map(str, q5)) + "]\nend Dim8Lift.Tab\n")
T5 = [l.split(' ', 1) for l in open(os.path.join(tdir, 'T5.txt'))]
rows5 = []
for l in open(os.path.join(tdir, 'T5.txt')):
    p = l.split(); rows5.append('(%s, %s, %s)' % (p[0], ' '.join(p[1:-1]), p[-1]))
rows6 = []
for l in open(os.path.join(tdir, 'T6.txt')):
    p = l.split(); rows6.append('(%s, %s, %s, %s)' % (p[0], p[1], ' '.join(p[2:-1]), p[-1]))
def write(name, rows, ty):
    n = 0; names = []
    for i in range(0, len(rows), chunk):
        nm = '%s%d' % (name, n); names.append(nm)
        with open(os.path.join(G, nm + '.lean'), 'w') as f:
            f.write("import TabDefs\n" + hdr + "namespace Dim8Lift.Tab\ndef %s : List (%s) := [\n" % (nm.lower(), ty) + ",\n".join(rows[i:i + chunk]) + "]\nend Dim8Lift.Tab\n")
        n += 1
    return names
n5 = write('T5c', rows5, 'Nat × List Nat × Nat')
n6 = write('T6c', rows6, 'Nat × Nat × List Nat × Nat')
with open(os.path.join(G, 'TabAll.lean'), 'w') as f:
    f.write(''.join('import %s\n' % x for x in n5 + n6) + "import Reps\nnamespace Dim8Lift.Tab\n"
            + "def t5 : List (Nat × List Nat × Nat) := " + " ++ ".join(x.lower() for x in n5) + "\n"
            + "def t6 : List (Nat × Nat × List Nat × Nat) := " + " ++ ".join(x.lower() for x in n6) + "\nend Dim8Lift.Tab\n")
open(os.path.join(G, 'modules.txt'), 'w').write(' '.join(['Reps'] + n5 + n6 + ['TabAll']))
print(len(n5), len(n6))
