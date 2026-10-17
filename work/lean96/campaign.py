"""Hidden standalone controller: validate one complete entry before scaling."""
from common import *
import subprocess,msvcrt
import psutil

def running(s):
    try:return psutil.Process(s['pid']).is_running() and abs(psutil.Process(s['pid']).create_time()-s['process_created'])<1
    except (psutil.Error,KeyError):return False

def main():
    guard=(OUT/'campaign.lock').open('a+b');guard.write(b'0');guard.flush();guard.seek(0)
    try:msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
    except OSError:raise SystemExit('Campaign controller already active')
    workers=int(sys.argv[1]) if len(sys.argv)>1 else 3
    def state(status):save(OUT/'campaign.json',dict(status=status,pid=os.getpid(),process_created=psutil.Process().create_time(),updated=now(),workers=workers))
    state('WAITING_FOR_EXISTING_RUNNER')
    while running(read(OUT/'progress.json',{})):time.sleep(5)
    s=read(OUT/'progress.json',{})
    if s.get('failures'):state('NEEDS_REPAIR');return
    if '118' not in s.get('entries',{}) or '118' not in s.get('representatives',{}):
        state('VALIDATING_REPRESENTATIVE')
        subprocess.run([sys.executable,'-X','utf8',str(HERE/'runner.py'),'--workers','1','--representatives','118'],cwd=ROOT)
        s=read(OUT/'progress.json',{})
    if '118' not in s.get('entries',{}) or '118' not in s.get('representatives',{}) or s.get('failures'):
        state('NEEDS_REPAIR');return
    # The representative gate has a complete geometric theorem and axiom audit.
    save(OUT/'representative-gate.json',dict(status='PASSED',entry=118,entry_record=s['entries']['118'],
        representative_record=s['representatives']['118'],time=now()))
    state('BATCH_RUNNING')
    subprocess.run([sys.executable,'-X','utf8',str(HERE/'runner.py'),'--workers',str(workers)],cwd=ROOT)
    state(read(OUT/'progress.json',{}).get('status','STOPPED_UNEXPECTEDLY'))

if __name__=='__main__':main()
