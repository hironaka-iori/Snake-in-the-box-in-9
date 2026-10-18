"""Single bounded solver process; parent enforces wall time; this enforces memory."""
import argparse
import ctypes
import os
import time
from common import *

_job = None


def memory_limit(mebibytes):
    global _job
    size = mebibytes * 1024**2
    if os.name != 'nt':
        import resource
        resource.setrlimit(resource.RLIMIT_AS,(size,size))
        return 'RLIMIT_AS'
    from ctypes import wintypes as w
    class Basic(ctypes.Structure):
        _fields_=[('process_time',ctypes.c_int64),('job_time',ctypes.c_int64),('flags',w.DWORD),
                  ('min_ws',ctypes.c_size_t),('max_ws',ctypes.c_size_t),('active',w.DWORD),
                  ('affinity',ctypes.c_size_t),('priority',w.DWORD),('scheduling',w.DWORD)]
    class IO(ctypes.Structure):
        _fields_=[(s,ctypes.c_uint64) for s in ['read_ops','write_ops','other_ops','read_bytes','write_bytes','other_bytes']]
    class Extended(ctypes.Structure):
        _fields_=[('basic',Basic),('io',IO),('process_memory',ctypes.c_size_t),
                  ('job_memory',ctypes.c_size_t),('peak_process',ctypes.c_size_t),('peak_job',ctypes.c_size_t)]
    k=ctypes.WinDLL('kernel32',use_last_error=True)
    k.CreateJobObjectW.argtypes=[ctypes.c_void_p,w.LPCWSTR];k.CreateJobObjectW.restype=w.HANDLE
    k.GetCurrentProcess.restype=w.HANDLE
    k.AssignProcessToJobObject.argtypes=[w.HANDLE,w.HANDLE]
    k.SetInformationJobObject.argtypes=[w.HANDLE,ctypes.c_int,ctypes.c_void_p,w.DWORD]
    _job=k.CreateJobObjectW(None,None)
    limits=Extended();limits.basic.flags=0x100;limits.process_memory=size
    if not _job or not k.SetInformationJobObject(_job,9,ctypes.byref(limits),ctypes.sizeof(limits)) or not k.AssignProcessToJobObject(_job,k.GetCurrentProcess()):
        raise ctypes.WinError(ctypes.get_last_error())
    return 'Windows Job Object PROCESS_MEMORY hard commit limit'


def diagnose(data, model, entry):
    values={abs(x):x>0 for x in model}
    if any(not any(values.get(abs(x)) == (x>0) for x in c) for c in data['clauses']):
        raise ValueError('solver model fails original CNF')
    selected={int(v) for v,i in data['selected'].items() if values.get(i,False)}
    adj={v:[v^(1<<k) for k in range(9) if v^(1<<k) in selected] for v in selected}
    unseen=set(selected);components=[]
    while unseen:
        todo=[min(unseen)];comp=set(todo);unseen.difference_update(comp)
        while todo:
            for x in adj[todo.pop()]:
                if x in unseen:
                    unseen.remove(x);comp.add(x);todo.append(x)
        components.append(sorted(comp))
    head=data['head'];trail=[head];previous=None
    while True:
        options=[v for v in adj[trail[-1]] if v != previous]
        if not options:break
        if len(options)!=1 or options[0] in trail:raise ValueError('head component not a path')
        previous=trail[-1];trail.append(options[0])
    candidate=bank()[entry][:95]+trail
    verify_path(candidate)
    full=len(candidate)==193 and set(trail)==selected
    return dict(cnf_model_verified=True,selected_vertices=len(selected),component_sizes=sorted(map(len,components)),
                head_component_vertices=len(trail),candidate_edges=len(candidate)-1,full_snake_verified=full,
                full_pair_checks=len(candidate)*(len(candidate)-1)//2,verified_head_path=candidate,
                disconnected_cycles=[c for c in components if head not in c])


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--entry',type=int,required=True)
    ap.add_argument('--memory-mib',type=int,required=True);ap.add_argument('--attempt',type=Path,required=True)
    a=ap.parse_args();policy=memory_limit(a.memory_mib)
    print('Memory policy:',policy,flush=True)
    from pysat.solvers import Solver
    formula_path=OUT/'formulas'/f'entry{a.entry:03d}.json.gz'
    data=json.loads(gzip.decompress(formula_path.read_bytes()))
    started=time.perf_counter()
    with Solver(name='g4',bootstrap_with=data['clauses'],with_proof=True) as solver:
        print('Solving Glucose 4.1; proof logging enabled; default solver parameters',flush=True)
        solved=solver.solve()
        result=dict(status='SAT' if solved else 'UNSAT',solver_seconds=time.perf_counter()-started,
                    statistics=solver.accum_stats(),memory_policy=policy)
        if solved:
            model=solver.get_model()
            compressed(a.attempt/'model.json.gz',json.dumps(model))
            result['diagnosis']=diagnose(data,model,a.entry)
        else:
            proof=solver.get_proof() or []
            compressed(a.attempt/'proof.drup.gz','\n'.join(proof)+'\n')
            result.update(certificate='proof.drup.gz',proof_lines=len(proof),certificate_validation='NOT_CHECKED',
                          interpretation='Solver UNSAT only; not a Lean proof')
        save(a.attempt/'worker-result.json',result)
        print(json.dumps(result),flush=True)


if __name__=='__main__':main()
