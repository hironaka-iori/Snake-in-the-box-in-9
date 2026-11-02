"""Replay the small count argument against the current window bridge."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sources={
 'ForcedShare':ROOT/'milestones/58-share-pressure/lean/ForcedShare.lean',
 'SplitShare':ROOT/'milestones/62-count-conditioned-share/lean/SplitShare.lean',
 'CountPropagation':ROOT/'milestones/65-count-saturation-share/lean/CountPropagation.lean',
 'CountChoice':ROOT/'milestones/65-count-saturation-share/lean/CountChoice.lean'}
texts={k:p.read_text() for k,p in sources.items()}
def section(key,start,end):
    text=texts[key];return text[text.index(start):text.index(end,text.index(start))].rstrip()
pieces=[section('ForcedShare','theorem count_mono','def forceCheck'),
 section('SplitShare','def forceCheckPlus','theorem mask_share_of_absent'),
 section('CountPropagation','theorem known_absent_count','theorem known_selected_count'),
 section('CountPropagation','def corners (','#print axioms count_complement'),
 section('CountChoice','def canonicalCentres','theorem count_choices_in_snake')]
text='import LocalWindowShareBridge\nimport LocalWindowDirBridge\nimport Mathlib.Tactic\n\nnamespace Snake9.LocalWindow.CountPropagation65\nset_option maxHeartbeats 2000000\n\n'
text+='\n\n'.join(pieces)+'\n\n'
for name in ['count_mono','forced_absent_plus','known_absent_count','corners_count','centresOf_canon']:text+=f'#print axioms {name}\n'
text+='end Snake9.LocalWindow.CountPropagation65\n'
(HERE/'lean/HistoryCountSupport.lean').write_text(text)
roots={}
for name,folder in [('TerminalCount','65-count-saturation-share'),('CountPhase04','66-full-model-and-revision'),('CountPhase29','66-full-model-and-revision')]:
    source=ROOT/'milestones'/folder/'lean'/f'{name}.lean';old=source.read_text()
    assert old.count('import CountChoice')==1 and old.count('open ForcedShare58 ExtendedShare59 SplitShare62')==1
    new=old.replace('import CountChoice','import HistoryCountSupport').replace('open ForcedShare58 ExtendedShare59 SplitShare62\n','')
    dest=HERE/'lean'/f'{name}.lean';dest.write_text(new)
    roots[name]=dict(source=source.relative_to(ROOT).as_posix(),source_sha256=sha(source),adapted_source_sha256=sha(dest),
      change='Import replaced and unused open command removed. All definitions and proof bodies unchanged; required helper definitions/proofs copied verbatim into the common parent namespace.')
out=dict(status='PREPARED_COMPATIBLE_COUNT_REPLAY',source_sha256={p.relative_to(ROOT).as_posix():sha(p) for p in sources.values()},
    roots=roots,support_source_sha256=sha(HERE/'lean/HistoryCountSupport.lean'),
    reason='The original CountChoice closure imports ShareFrame, whose declarations collide with the current LocalWindowShareBridge. The required helper declarations and three count proofs are replayed in the current environment.',
    scope='Compatibility extraction only. Fresh successful Lean receipts are required before use; the original object-overlay import attempt is rejected.')
(HERE/'data/compatible-count-sources.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],'five helper theorem bodies and three count proof modules')
