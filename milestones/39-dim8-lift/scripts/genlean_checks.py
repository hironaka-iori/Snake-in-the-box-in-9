"""(Re)write the table check modules in lean/gen without touching the data modules.
t5 chunks: one `decide +kernel` each; t6 chunks: four parts of 500 entries (memory), combined by
`all_parts`.  Also writes gen/checks.txt and gen/Final229.lean."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
G = os.path.join(HERE, '..', 'lean', 'gen')
mods = open(os.path.join(G, 'modules.txt')).read().split()
n5 = [m for m in mods if m.startswith('T5c')]; n6 = [m for m in mods if m.startswith('T6c')]
P6 = "(fun e => chk 6 e.2.1 e.2.2.1 e.2.2.2 && reps.contains (pcN 64 e.2.2.2, e.2.2.2))"
hdr = "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Dim8Lift.Tab\n"
chk = []
for nm in n5:
    chk.append(nm + 'Ok')
    open(os.path.join(G, nm + 'Ok.lean'), 'w').write("import %s\n" % nm + hdr +
        "theorem %s_ok : %s.all (fun e => chk 5 e.1 e.2.1 e.2.2) = true := by decide +kernel\nend Dim8Lift.Tab\n" % (nm.lower(), nm.lower()))
parts = ["(%s.take 500)", "((%s.drop 500).take 500)", "((%s.drop 1000).take 500)", "(%s.drop 1500)"]
for nm in n6:
    for p, e in enumerate(parts):
        chk.append('%sP%dOk' % (nm, p))
        open(os.path.join(G, '%sP%dOk.lean' % (nm, p)), 'w').write("import %s\nimport Reps\nimport CoverDefs\n" % nm + hdr +
            "theorem %s_p%d : %s.all %s = true := by decide +kernel\nend Dim8Lift.Tab\n" % (nm.lower(), p, e % nm.lower(), P6))
    chk.append(nm + 'Ok')
    open(os.path.join(G, nm + 'Ok.lean'), 'w').write(''.join("import %sP%dOk\n" % (nm, p) for p in range(4)) + "import TabParts\n" + hdr +
        "theorem %s_ok : %s.all %s = true :=\n  all_parts _ _ %s\nend Dim8Lift.Tab\n"
        % (nm.lower(), nm.lower(), P6, ' '.join('%s_p%d' % (nm.lower(), p) for p in range(4))))
with open(os.path.join(G, 'Final229.lean'), 'w') as f:
    f.write(''.join('import %s\n' % (x + 'Ok') for x in n5 + n6) + "import TabAll\nimport Final\n"
            "/-! a(9) <= 229 from the cover and cube certificates (the only remaining premises). -/\n"
            "namespace Dim8Lift.Tab\nopen Dim8Lift.Cube Snake9.LocalWindow\n\n"
            "theorem t5_ok : t5.all (fun e => chk 5 e.1 e.2.1 e.2.2) = true := by\n  simp only [t5, List.all_append, "
            + ", ".join(x.lower() + '_ok' for x in n5) + ", Bool.and_self]\n\n"
            "theorem t6_ok : t6.all " + P6 + " = true := by\n  simp only [t6, List.all_append, "
            + ", ".join(x.lower() + '_ok' for x in n6) + ", Bool.and_self]\n\n"
            "theorem upper_229_of_unsat (hU5 : Unsat (c5Cnf (t5.map (·.1))))\n"
            "    (hU6 : ∀ e ∈ t5, Unsat (c6Cnf e.2.2 ((t6.filter (·.1 == e.2.2)).map (·.2.1))))\n"
            "    (hcubes : ∀ r ∈ reps, Unsat (cubeCnfC4 13 116 r.2 r.1)) : ∀ {m : Nat}, Snake9.Snake m → m ≤ 229 :=\n"
            "  Dim8Lift.upper_of_certs (L := 116) (by decide) (by decide) t5 t6 reps t5_ok t6_ok hU5 hU6 hcubes\n\n"
            "end Dim8Lift.Tab\n\n#print axioms Dim8Lift.Tab.upper_229_of_unsat\n")
open(os.path.join(G, 'checks.txt'), 'w').write(' '.join(chk + ['Final229']))
print(len(chk))
