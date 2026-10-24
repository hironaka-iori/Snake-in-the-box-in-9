from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
r=json.loads((HERE/'data/verification.json').read_text());assert r['status']=='PASSED'
intro='''The latest local result is [milestone 40](milestones/40-intervening-counts/README.md). For directions (a,b,c,d,e,c,a,d), if the first and seventh internal singleton counts are both at most three, then the third and sixth counts are each at least five. Eight Lean audits passed, including both refutations and arbitrary coordinate normalization. These restrictions eliminate the saved 119/29 diagnostic cycle at its identified occurrence. Twenty-three independent local forest checks establish local attainments and controls; no new global bound or minimum cycle mean is claimed. The strongest manuscript interval remains 191 <= a(9) <= 236.

'''
for name in ['README.md','COLLABORATION.md','WORKSPACE.md']:
 p=ROOT/name;s=p.read_text(encoding='utf-8');anchor='The current manuscript interval is **191 <= a(9) <= 236**.'
 assert anchor in s;s=s.replace(anchor,intro+anchor,1)
 if name=='COLLABORATION.md':
  a=s.index('Next: use the surviving lower-table cycle');b=s.index('\n\n',a)
  s=s[:a]+'''Next: certify the joint sum of the third and sixth counts. The numerical threshold is 12 under the same two distant-count caps, with an independently checked local forest attaining 12. The five intervening counts similarly have numerical threshold 24. These require a joint-counter interpretation and fresh refutation replay; adding the proved individual bounds yields only 10. Once a joint theorem is established, rebuild the diagnostic automaton with sufficient memory and a common overlap budget. The old critical cycle has been excluded, but no replacement minimum has been established.'''+s[b:]
  a=s.index('Latest GitHub refresh (24 October):');b=s.index('\n\n',a)
  s=s[:a]+'''Latest GitHub refresh (24 October): `research/unconditional-241` is at `b92c8da2`, regenerating the six-centre 235 automaton and aggregate modules; its recorded completed global theorem remains 236 at 7cb52aad. `claude/relaxed-keller-60ks7i` is at `8e9144df`, following checked share refutations and a share theorem toward 234; its final 234 template still has a refutation premise. This checkpoint does not promote those incomplete aggregate claims to new global theorems.'''+s[b:]
 p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'milestones/README.md';s=p.read_text(encoding='utf-8')
s+='\n- [40: Intervening-count restrictions](40-intervening-counts/README.md): two new three-position implications, eight Lean audits, 23 checked local forests, a saved cyclic relaxation, and exclusion of the identified low-mean cycle occurrence.\n'
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text(encoding='utf-8')
s+='''
## 24 October 2026: intervening-count restrictions

The preceding round made verified progress by incorporating the audited 236 theorem and its full manuscript argument. This round tests the surviving lower-table cycle, rather than assuming its compatibility from pair inequalities. Its reversed phase 18 has directions 01234203 and counts (3,4,4,5,5,3,3). Two new universal local implications now exclude that occurrence: first and seventh counts at most 3 force both third and sixth counts at least 5. The two cores have 2708/1419 clauses and 1141561/86400 LRAT hints. Both refutations, geometric interpretations, and arbitrary coordinate normalization passed eight Lean audits. Twenty-three local forests have independent checks. The degree-and-endpoint relaxation admits a 142-vertex configuration with three cycles, showing why cycle exclusions matter to this local proof. The second certificate's four cycle cuts are translates of one induced ten-cycle. Joint thresholds 12 and 24 have numerical support and local attainments but remain unproved. No new global bound or minimum cycle mean is claimed; the paper's interval remains 191..236. The paper and existing editor were updated with authors and settings preserved; preview preparation remains blocked before TeX by the Windows runner.
'''
p.write_text(s,encoding='utf-8',newline='\n')
p=HERE/'README.md';s=p.read_text(encoding='utf-8')
s=s.replace('The authoritative completion gate is `data/verification.json`; proof generation alone does not establish completion. Its gate requires both full kernel replays, four interpretation audits and four normalization/consequence audits, all with standard axioms only.','The completion gate `data/verification.json` passed: both full kernel replays, four refutation/interpretation audits and four normalization/consequence audits use only standard axioms. All 23 saved local forests passed independent checks.')
p.write_text(s,encoding='utf-8',newline='\n')
