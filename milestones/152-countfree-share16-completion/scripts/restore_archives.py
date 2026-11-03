"""Restore only missing archived query files, checking existing bytes first."""
from pathlib import Path
import hashlib,json,zipfile
H=Path(__file__).resolve().parents[1]
record=json.loads((H/'data/strengthening-archive.json').read_text(encoding='utf-8-sig'))
archive=H/record['archive']; sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(archive.read_bytes())==record['sha256']
with zipfile.ZipFile(archive) as z:
    for item in record['members']:
        target=(H/item['path']).resolve(); assert target.is_relative_to(H.resolve())
        data=z.read(item['path']);assert len(data)==item['bytes'] and sha(data)==item['sha256']
        if target.exists():assert sha(target.read_bytes())==item['sha256']
        else:
            target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
print('PASS_ARCHIVED_QUERY_FILES_PRESENT')
