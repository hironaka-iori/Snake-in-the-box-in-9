# gdb -p PID -batch -x pmp.py   (env PMP_N samples, PMP_DT seconds, PMP_OUT file)
import gdb, os, signal, threading, time
N=int(os.environ.get('PMP_N','40')); DT=float(os.environ.get('PMP_DT','0.25')); OUT=os.environ['PMP_OUT']
pid=gdb.selected_inferior().pid
gdb.execute('handle SIGINT stop nopass', to_string=True)
gdb.execute('set pagination off')
out=open(OUT,'w')
for i in range(N):
    def k():
        time.sleep(DT)
        try: os.kill(pid, signal.SIGINT)
        except Exception: pass
    threading.Thread(target=k,daemon=True).start()
    try:
        gdb.execute('continue', to_string=True)
    except Exception as e:
        break
    try:
        s=gdb.execute('thread apply all bt 60', to_string=True)
    except Exception as e:
        break
    out.write('=== %d\n%s\n'%(i,s)); out.flush()
out.close()
gdb.execute('detach')
