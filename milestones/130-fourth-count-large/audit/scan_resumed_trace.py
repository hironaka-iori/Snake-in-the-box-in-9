"""Check whether the terminal timeout trace contains an empty-clause record."""
from pathlib import Path
import datetime,hashlib,json
H=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record=H/'data/search-resumed.json';r=json.loads(record.read_text())
assert r['status']=='TIMEOUT'
raw=H/'work/large-resumed.raw.lrat';before=sha(raw)
assert before==r['raw_sha256'] and raw.stat().st_size==r['raw_bytes']
rows=dict(physical_records=0,deduction_like_records=0,deletion_records=0,empty_clause_records=0)
last=b''
with raw.open('rb') as f:
 for line in f:
  parts=line.split(None,2);assert len(parts)>=2
  rows['physical_records']+=1
  if parts[1]==b'd':rows['deletion_records']+=1
  else:
   rows['deduction_like_records']+=1
   rows['empty_clause_records']+=parts[1]==b'0'
  last=line
rows.update(final_line_terminated=last.endswith(b'\n'),final_record_ends_in_zero=last.split()[-1:]==[b'0'])
assert sha(raw)==before
out=dict(status='PASS_TIMEOUT_TRACE_RECORD_SCAN',completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 raw_sha256=before,raw_bytes=raw.stat().st_size,terminal_record_sha256=sha(record),scan=rows,
 script_sha256=sha(Path(__file__)),scope='This is a textual record scan only. It does not replay deductions beyond the separately checked 5000-step prefix.')
dest=H/'data/large-resumed-scan.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
