import urllib.request, json, zipfile, io
from pathlib import Path

target = Path('work/solver_packages').resolve()
target.mkdir(exist_ok=True)
packages = [('ortools', None), ('absl-py', None), ('numpy', None), ('pandas', None),
            ('protobuf', '6.33.5'), ('typing-extensions', None), ('immutabledict', None),
            ('python-dateutil', None), ('six', None), ('tzdata', None)]
for package, version in packages:
    suffix = f'/{version}' if version else ''
    data = json.load(urllib.request.urlopen(f'https://pypi.org/pypi/{package}{suffix}/json'))
    choices = [x for x in data['urls'] if x['filename'].endswith('.whl') and (
        'cp312-cp312-win_amd64' in x['filename'] or
        'py3-none-any' in x['filename'] or 'py2.py3-none-any' in x['filename'] or
        ('abi3-win_amd64' in x['filename'] and any(f'cp{v}-' in x['filename'] for v in [39,310,311,312])))]
    assert choices, (package, [x['filename'] for x in data['urls']])
    wheel = choices[0]
    raw = urllib.request.urlopen(wheel['url']).read()
    import hashlib
    assert hashlib.sha256(raw).hexdigest() == wheel['digests']['sha256']
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        for entry in archive.infolist():
            dst = (target / entry.filename).resolve()
            assert dst.is_relative_to(target)
            if entry.is_dir():
                dst.mkdir(parents=True, exist_ok=True)
            else:
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes(archive.read(entry))
    print(wheel['filename'], flush=True)
