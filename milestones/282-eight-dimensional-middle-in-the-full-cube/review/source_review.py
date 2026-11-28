"""Compare both final manuscripts with the previous written-source review."""
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
PRIOR=next((ROOT/'milestones').glob('270-*'))/'review'
spec=spec_from_file_location('previous_source_review',PRIOR/'coverage.py')
review=module_from_spec(spec)
spec.loader.exec_module(review)
review.BASE='b9560007c180b8fa5a452ad98cfe97c5f9c05de3'
prior=json.loads((PRIOR/'source-coverage.json').read_bytes())
results={}
for name in prior:
    row=review.compare(ROOT,name,None,prior)
    authoritative=Path('D:/Codex/2026-10-13/new-chat/outputs')/(name+'.tex')
    assert sha256(authoritative.read_bytes()).hexdigest()==row['reviewed_sha256']
    results[name]=row
(HERE/'source-coverage.json').write_bytes((json.dumps(results,indent=2)+'\n').encode())
print({k:(r['reviewed_lines'],r['added_or_replaced_lines']) for k,r in results.items()})
