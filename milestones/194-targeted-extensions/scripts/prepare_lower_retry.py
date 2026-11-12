from pathlib import Path
H=Path(__file__).resolve().parents[1]
source=(H/'scripts/retry_solver_pinned.py').read_text()
for before,after in [("bank9-input.json","lower-input.json"),("range(512)","range(128)"),("range(9)","range(7)"),("range(bit1+1,9)","range(bit1+1,7)"),("len(full)==193","len(full)==50")]:
    assert before in source,before
    source=source.replace(before,after)
target=H/'scripts/lower_retry.py';assert not target.exists();target.write_text(source,encoding='utf-8',newline='\n')
print('PREPARED_LOWER_RETRY')
