import subprocess, os, time, sys
S=os.environ.get('STUDY', '/tmp/replay-study')
LEAN=os.environ.get('LEAN', os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.19.0/bin/lean'))
LIB=os.path.join(os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')), 'work', 'final_lean', '.lake', 'build', 'lib', 'lean')
tag, mod, imports, opens = sys.argv[1], sys.argv[2], sys.argv[3].split(','), sys.argv[4]
env=dict(os.environ, LEAN_PATH=S+'/oleanstudy/'+tag+'/_olean:'+S+'/oleanstudy/lib:'+LIB)
for prop in sys.argv[5:]:
    src='\n'.join(['import LocalWindowUnsat.%s.%s' % (mod, i) for i in imports] + ['import '+x for x in opens.split(',') if x] +
        ['set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option Elab.async false',
         'namespace Snake9.LocalWindow.'+mod,'open Snake9.LratFastO4k','open Snake9.LratFast2_O4k','open Snake9.LratFast2F_O4k','open Snake9.LratFast2L_O4k',
         'open Snake9.LratO4k (Tree TreeTrue andB)','theorem t : %s := by' % prop,'  decide +kernel','end Snake9.LocalWindow.'+mod,''])
    f=S+'/micro_t.lean'; open(f,'w').write(src)
    t=time.time(); p=subprocess.Popen(['nice','-n','15',LEAN,f],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    out=p.stdout.read(); _,st,ru=os.wait4(p.pid,0)
    print('%-70s st=%d cpu=%.2f rss=%.2f %s' % (prop[:70], st, ru.ru_utime+ru.ru_stime, ru.ru_maxrss/1e6, out[-200:].decode().strip()[:200] if st else ''), flush=True)
