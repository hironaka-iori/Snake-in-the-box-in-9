from control_common import *
for i in range(4,len(p)-4):
    for a in range(9):
        for b in range(a):
            def f(x):
                return x^((1<<a)|(1<<b)) if ((x^p[i])>>a^(x^p[i])>>b)&1 else x
            q=p[:i]+[f(x) for x in p[i:]]
            if len(defects(q) or [])!=1:continue
            r=subprocess.run(['/tmp/q9_binary_isometries_20261121','2','0','1','923'],input=' '.join(map(str,q))+'\n',capture_output=True,text=True,check=True).stdout
            assert r.startswith('FOUND')
            w=list(map(int,r.split('vertices')[1].split()))
            assert len(w)==len(q) and defects(w)==[]
            print('control seed row 0, suffix pivot',i,a,b,'injected chord',defects(q),'recovered',len(w)-1,'edges; '+r.strip())
            raise SystemExit(0)
raise ValueError('could not generate damaged control')
