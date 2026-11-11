from pathlib import Path
import hashlib,json
R=Path('E:/Snake-in-a-box');H=R/'milestones/191-coloured-replacements';P=R/'milestones/190-exchange-constraints'
assert not H.exists(), 'Preserve any existing round191 work.'
for n in ['data','scripts','lean','build','logs']:(H/n).mkdir(parents=True,exist_ok=True)
(H/'.gitattributes').write_text('* -text\n')
for n in ['check_core.py','native_resources.py']:(H/'scripts'/n).write_bytes((P/'scripts'/n).read_bytes())
(H/'data/middle95.json').write_bytes((P/'data/middle95.json').read_bytes())
(H/'scripts/replacements.py').write_bytes(Path(__file__).with_name('round191_replacements.py').read_bytes())
(H/'scripts/prepare.py').write_bytes(Path(__file__).read_bytes())
(H/'data/start.json').write_text(json.dumps({'round':191,'parent_commit':'edb646632780c6f9f023a1c525eef2557a2b3eae','start_utc':'2026-11-11 04:37:56 UTC','direction':'dimension lifting via fixed-port middle replacements','pause_after_round':True,'middle_sha256':hashlib.sha256((H/'data/middle95.json').read_bytes()).hexdigest()},indent=2)+'\n')
print(H)
