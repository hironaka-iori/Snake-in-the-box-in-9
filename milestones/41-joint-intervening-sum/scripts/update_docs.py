from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
receipt=json.loads((HERE/'data/verification.json').read_text());assert receipt['status']=='PASSED'
text='''The latest theorem is [milestone 41](milestones/41-joint-intervening-sum/README.md). For directions (a,b,c,d,e,c,a,d), first and seventh internal singleton counts at most three imply that the third and sixth counts sum to at least 12. Ten Lean audits passed, including a generic counter identity, the 5,222,602-hint replay, exact geometric interpretation, and overlap accounting. If the corresponding truncated counts sum to at most 11, each occurrence forces one excess unit; multiplicity two gives 12 charge units per occurrence. No occurrence-frequency lower bound is known. All 131 bank paths were checked: 1,442 direction-pattern occurrences, none meeting the two low-count caps. The global interval remains 191 <= a(9) <= 236.

'''
for name in ['README.md','COLLABORATION.md','WORKSPACE.md']:
 p=ROOT/name;s=p.read_text(encoding='utf-8');anchor='The latest local result is [milestone 40]'
 assert anchor in s;s=s.replace(anchor,text+'The preceding local result is [milestone 40]',1)
 if name=='COLLABORATION.md':
  a=s.index('Next: certify the joint sum');b=s.index('\n\n',a)
  s=s[:a]+'''Next: use the new sum theorem in a state model that retains the required count history and shares one excess budget across overlapping patterns. This must establish a bound for every allowed sequence, rather than only remove the saved critical cycle. The proposed sum24 over five intervening centres remains numerical; the new generic counter lemma supports its interpretation, but a separate replay is required. No 192-edge witness or exact optimum has been established.'''+s[b:]
 p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'milestones/README.md';s=p.read_text(encoding='utf-8')
s+='\n- [41: Joint intervening-count bound and excess accounting](41-joint-intervening-sum/README.md): sum12 theorem, ten Lean audits, conditional charge contribution, and full published-bank controls.\n'
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text(encoding='utf-8')
s+='''
## 24 October 2026: joint intervening sum and overlap accounting

The preceding goal round made progress by proving both individual thresholds5, compiling the revised paper, and pushing the checkpoint. Milestone41 proves the stronger joint threshold12 under the same two distant-count caps. A generic concatenated-counter identity preserves multiplicities; the 4097-clause core with1401 active variables was replayed using5222602 hints in174 segments and29 check modules. All208 recorded build modules succeeded. Ten final dependency audits cover the counter, clause interpretation, arbitrary-snake theorem, and excess accounting. A qualifying truncated sum at most11 forces one count-excess unit, giving a conditional charge contribution of12 per occurrence after multiplicity-two accounting. This shares the existing excess budget. Independent checks of all131 bank paths find1442 oriented pattern occurrences and zero qualifying low-count occurrences, so there is no frequency claim. The local forest attaining12 was independently rechecked. The five-centre sum24 remains numerical. The paper and existing editor source were updated and compiled successfully; visual inspection of every rendered page remains undone. The global interval remains191..236.
'''
for a,b in [('thresholds5','thresholds 5'),('Milestone41','Milestone 41'),('threshold12','threshold 12'),('with1401','with 1401'),('using5222602','using 5222602'),('in174','in 174'),('and29','and 29'),('All208','All 208'),('most11','most 11'),('of12','of 12'),('all131','all 131'),('find1442','find 1442'),('attaining12','attaining 12'),('sum24','sum 24'),('remains191..236','remains 191..236')]:s=s.replace(a,b)
p.write_text(s,encoding='utf-8',newline='\n')
