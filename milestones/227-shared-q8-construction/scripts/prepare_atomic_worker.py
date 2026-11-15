"""Preserve the initial worker and create its atomic-frontier successor."""
from pathlib import Path
H=Path(__file__).resolve().parents[1]
p=H/'scripts/shared_paths.py';s=p.read_text(encoding='utf-8')
changes=[
("counts['all_options_pruned']+=1;state['first_frontier'].pop();continue", "counts['all_options_pruned']+=1;state=dict(state,first_frontier=state['first_frontier'][:-1]);continue"),
("state.update(phase='second',pending_options=options,second_frontier=[[tasks[options[0]]['u']]])", "state=dict(state,phase='second',pending_options=options,second_frontier=[[tasks[options[0]]['u']]])"),
("state['first_frontier'].pop()\n                state['first_frontier'].extend(dict(path=q,options=options) for q in children or [])", "state=dict(state,first_frontier=state['first_frontier'][:-1]+[dict(path=q,options=options) for q in children or []])"),
("counts['second_exhaustions']+=1;state['pending_options'].pop(0)\n                if state['pending_options']:state['second_frontier']=[[tasks[state['pending_options'][0]]['u']]]\n                else:state['phase']='first';state['first_frontier'].pop()", "counts['second_exhaustions']+=1;remaining_options=state['pending_options'][1:]\n                if remaining_options:state=dict(state,pending_options=remaining_options,second_frontier=[[tasks[remaining_options[0]]['u']]])\n                else:state=dict(state,phase='first',first_frontier=state['first_frontier'][:-1],pending_options=[],second_frontier=[])"),
("state['second_frontier'].pop();state['second_frontier'].extend(children or [])", "state=dict(state,second_frontier=state['second_frontier'][:-1]+(children or []))")]
for old,new in changes:assert s.count(old)==1;s=s.replace(old,new)
out=H/'scripts/shared_paths_atomic.py';assert not out.exists();out.write_text(s,encoding='utf-8')
runner=(H/'scripts/run_shared.py').read_text(encoding='utf-8').replace('shared_paths.py','shared_paths_atomic.py')
(H/'scripts/run_shared_atomic.py').write_text(runner,encoding='utf-8')
print('PREPARED_ATOMIC_WORKER_WITH_UNCHANGED_SEARCH_RULES')
