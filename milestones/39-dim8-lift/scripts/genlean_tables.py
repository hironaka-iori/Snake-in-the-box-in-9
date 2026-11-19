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

# chunk checks (decide +kernel) and the instantiated final theorem
chk = []
for nm in n5:
    chk.append(nm + 'Ok')
    with open(os.path.join(G, nm + 'Ok.lean'), 'w') as f:
        f.write("import %s\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Dim8Lift.Tab\n"
                "theorem %s_ok : %s.all (fun e => chk 5 e.1 e.2.1 e.2.2) = true := by decide +kernel\nend Dim8Lift.Tab\n"
                % (nm, nm.lower(), nm.lower()))
for nm in n6:
    chk.append(nm + 'Ok')
    with open(os.path.join(G, nm + 'Ok.lean'), 'w') as f:
        f.write("import %s\nimport Reps\nimport CoverDefs\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Dim8Lift.Tab\n"
                "theorem %s_ok : %s.all (fun e => chk 6 e.2.1 e.2.2.1 e.2.2.2 && reps.contains (pcN 64 e.2.2.2, e.2.2.2)) = true := by\n  decide +kernel\nend Dim8Lift.Tab\n"
                % (nm, nm.lower(), nm.lower()))
with open(os.path.join(G, 'Final229.lean'), 'w') as f:
    f.write(''.join('import %s\n' % x for x in chk) + "import TabAll\nimport Final\n"
            "/-! a(9) <= 229 from the cover and cube certificates (the only remaining premises). -/\n"
            "namespace Dim8Lift.Tab\nopen Dim8Lift.Cube Snake9.LocalWindow\n\n"
            "theorem t5_ok : t5.all (fun e => chk 5 e.1 e.2.1 e.2.2) = true := by\n  simp only [t5, List.all_append, "
            + ", ".join(x.lower() + '_ok' for x in n5) + ", Bool.and_self]\n\n"
            "theorem t6_ok : t6.all (fun e => chk 6 e.2.1 e.2.2.1 e.2.2.2 && reps.contains (pcN 64 e.2.2.2, e.2.2.2)) = true := by\n  simp only [t6, List.all_append, "
            + ", ".join(x.lower() + '_ok' for x in n6) + ", Bool.and_self]\n\n"
            "theorem upper_229_of_unsat (hU5 : Unsat (c5Cnf (t5.map (·.1))))\n"
            "    (hU6 : ∀ e ∈ t5, Unsat (c6Cnf e.2.2 ((t6.filter (·.1 == e.2.2)).map (·.2.1))))\n"
            "    (hcubes : ∀ r ∈ reps, Unsat (cubeCnfC4 13 116 r.2 r.1)) : ∀ {m : Nat}, Snake9.Snake m → m ≤ 229 :=\n"
            "  Dim8Lift.upper_of_certs (L := 116) (by decide) (by decide) t5 t6 reps t5_ok t6_ok hU5 hU6 hcubes\n\n"
            "end Dim8Lift.Tab\n\n#print axioms Dim8Lift.Tab.upper_229_of_unsat\n")
open(os.path.join(G, 'checks.txt'), 'w').write(' '.join(chk + ['Final229']))
print('checks', len(chk))
