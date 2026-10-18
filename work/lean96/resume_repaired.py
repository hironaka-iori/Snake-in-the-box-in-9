"""One repair validation gate, followed by one bounded retry of the full queue."""
from common import *
from campaign import running
import subprocess,msvcrt
import psutil

def main():
    guard=(OUT/'campaign.lock').open('a+b');guard.write(b'0');guard.flush();guard.seek(0)
    try:msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
    except OSError:raise SystemExit('Another controller holds the campaign lock')
    workers=int(sys.argv[1]) if len(sys.argv)>1 else 2
    def record(status):save(OUT/'campaign.json',dict(status=status,pid=os.getpid(),process_created=psutil.Process().create_time(),updated=now(),workers=workers,validation_entry=179))
    record('WAITING_FOR_REPAIR_VALIDATION')
    while running(read(OUT/'progress.json',{})):time.sleep(5)
    s=read(OUT/'progress.json',{})
    if '179' not in s.get('representatives',{}) or '179' not in s.get('entries',{}) or '179' in s.get('failures',{}):
        record('NEEDS_REPAIR');return
    save(OUT/'repair-gate.json',dict(status='PASSED',entry=179,representative=s['representatives']['179'],
        entry_record=s['entries']['179'],generator_sha256=sha(HERE/'export_local_rup.py'),time=now()))
    record('BATCH_RUNNING')
    subprocess.run([sys.executable,'-X','utf8',str(HERE/'runner.py'),'--workers',str(workers),'--retry-failures'],cwd=ROOT)
    record(read(OUT/'progress.json',{}).get('status','STOPPED_UNEXPECTEDLY'))
if __name__=='__main__':main()
