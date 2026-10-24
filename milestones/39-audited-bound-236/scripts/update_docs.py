from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
intro='''The current manuscript interval is **191 <= a(9) <= 236**. [Milestone 39](milestones/39-audited-bound-236/README.md) incorporates the completed radius-four theorem from contributor commit `7cb52aad`, with all 732 window refutations and a successful saved Linux dependency audit. The paper now supplies its full potential, boundary, endpoint, and incidence argument. An independent local enumeration checks 1,026,432 candidate transitions, and four new Lean arithmetic checks passed. The complete contributor proof has not been independently rebuilt here; selected proof interfaces and audit receipts are pinned separately from the earlier local proof build.

'''
for name in ['README.md','COLLABORATION.md','WORKSPACE.md']:
 p=ROOT/name;s=p.read_text(encoding='utf-8')
 anchor='The latest research checkpoint is [milestone 38]'
 assert anchor in s
 s=s.replace(anchor,intro+'The preceding research checkpoint is [milestone 38]',1)
 # Keep dated historical checkpoints accurate without presenting them as current.
 s=s.replace('the integrated interval remains 191 <= a(9) <= 238.','the integrated interval at that checkpoint was 191 <= a(9) <= 238.')
 s=s.replace('The integrated interval remains 191 <= a(9) <= 238.','The integrated interval at that checkpoint was 191 <= a(9) <= 238.')
 if name=='COLLABORATION.md':
  a=s.index('Latest GitHub refresh (24 October):');b=s.index('\n\n',a)
  s=s[:a]+'''Latest GitHub refresh (24 October): `research/unconditional-241` advanced to `7cb52aad`, completing the 236 theorem and all 732 kernel replays. Milestone39 reviews its final theorem and saved audit, and incorporates the result in the paper without replacing the revised manuscript with the branch's older layout. `claude/relaxed-keller-60ks7i` advanced to `c1da9a75`, adding work toward the share bridge for 234; that bridge remains marked in progress. `research/unconditional-231-230` remains at `e931afe8`. No 234/235 theorem is asserted by this checkpoint.'''+s[b:]
 if name=='README.md':
  anchor='| A 191-edge snake exists | Explicit witness checked in Lean |'
  s=s.replace(anchor,anchor+'\n| Every snake has at most 236 edges | Completed contributor theorem at pinned commit `7cb52aad`; all 732 refutations and final Linux dependency audit recorded; local independent table and arithmetic checks passed, clean full rebuild pending |',1)
 p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'milestones/README.md';s=p.read_text(encoding='utf-8')
s+='\n- [39: Audited radius-four bound of 236](39-audited-bound-236/README.md): pinned contributor theorem, complete exclusion catalogue, independent potential checks, four new Lean arithmetic checks, and revised manuscript proof.\n'
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text(encoding='utf-8')
s+='''
## 24 October 2026: integrate the audited 236 theorem

Reviewed contributor commit 7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b. Its final theorem discharges all 732 radius-four window exclusions and its saved Linux audit lists only standard axioms. Milestone39 pins 12 proof interfaces and receipts plus all 732 keys. It does not claim a fresh local rebuild of the complete replay closure. Independent enumeration passed all 1,026,432 candidate transitions, with 611,613 permitted, and four new Lean arithmetic audits passed. The actual potential maximum is 48; the checked summation uses the valid weaker bound63 and hence boundary291. The paper now explains this choice and proves the 236 conclusion with all endpoint terms explicit. Its principal interval is 191 <= a(9) <= 236. Authors, hyperlink settings, prior statements except the strengthened principal theorem, and witness appendix are preserved. The existing editor is synchronized; preview preparation still fails before TeX in the Windows runner.
'''
p.write_text(s,encoding='utf-8',newline='\n')
