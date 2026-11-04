"""Restore missing archived inputs; reject changed existing files."""
from pathlib import Path
import hashlib,json,zipfile
H=Path(__file__).resolve().parents[1]
record=json.loads((H/'data/archives.json').read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
for item in record['archives']:
    archive=H/item['path'];assert sha(archive.read_bytes())==item['sha256']
    with zipfile.ZipFile(archive) as z:
        for row in item['members']:
            target=(H/row['path']).resolve();assert target.is_relative_to(H.resolve())
            data=z.read(row['path']);assert len(data)==row['bytes'] and sha(data)==row['sha256']
            if target.exists():assert sha(target.read_bytes())==row['sha256']
            else:
                target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
print('PASS_ARCHIVED153_FILES_PRESENT')
