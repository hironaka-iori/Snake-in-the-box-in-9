"""Induced paths via directed modular ranks, with certified cycle cuts."""
import argparse
import json
import subprocess
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import build, read_path
from q9_endpoint_lex import add_endpoint_lex
from q9_free_pair_cuts import add_pair_cuts
from verify_q9_free_dimension_cuts import parts, deg


def phase_variables(f,pool,n,bits,length,end):
    phase = [[pool.id() for _ in range(bits)] for v in range(n)]
    bump = []
    for v, row in enumerate(phase):
        # Phase represents (path position - Hamming weight) / 2 modulo 2^bits.
        a = [-row[0]]
        carry = row[0]
        for i, bit in enumerate(row[1:], start=1):
            total = pool.id()
            f.extend([[-carry,-bit,-total],[carry,bit,-total],
                      [carry,-bit,total],[-carry,bit,total]])
            a.append(total)
            if i < bits-1:
                following = pool.id()
                f.extend([[-following,carry],[-following,bit],[-carry,-bit,following]])
                carry = following
        bump.append(a)
        if v in (0,end):
            number = (length-end.bit_count())//2 if v == end else 0
            f.extend([[literal if number >> i & 1 else -literal] for i,literal in enumerate(row)])
    return phase, bump


def add_counted_edge_phase(f,pool,n,bits,length,end,physical,terminal_windows=False):
    """Use the physical edge literals already counted by the frequency model."""
    phase, bump = phase_variables(f,pool,n,bits,length,end)
    if terminal_windows:
        assert length < 2 << bits
        from q9_anchor_distances import add_distances, add_terminal_neighbor_distances

        add_distances(f,phase,[(0,0),(end,length)],length)
        add_terminal_neighbor_distances(f,phase,end,length)
    incoming = [[] for _ in range(n)]
    outgoing = [[] for _ in range(n)]
    for u,v,edge in physical:
        up,down = pool.id(),pool.id()
        f.extend([[-up,edge],[-down,edge],[-edge,up,down],[-up,-down]])
        outgoing[u].append(up)
        incoming[v].append(up)
        outgoing[v].append(down)
        incoming[u].append(down)
        for x,y,z in zip(phase[u],phase[v],bump[v]):
            f.extend([[-up,-x,y],[-up,x,-y],[-down,-x,z],[-down,x,-z]])
    for v in range(n):
        if v == 0:
            f.extend([[-a] for a in incoming[v]])
        else:
            f.append([-v-1,*incoming[v]])
        if v == end:
            f.extend([[-a] for a in outgoing[v]])
        else:
            f.append([-v-1,*outgoing[v]])


def modular(dim, length, distance, bits, pair17=False, lex=False, census=False, triple=None, anchors=(), anchor_distances=False, half_membership=False, prefix_cuts=(), axis_windows=()):
    f, end = build(dim,length,distance,include_rank=False)
    n = 1 << dim
    pool = IDPool(start_from=f.nv+1)
    phase, bump = phase_variables(f,pool,n,bits,length,end)
    if census:
        modulus = 2 << bits
        for residue in range(modulus):
            occupancy = []
            for v,row in enumerate(phase):
                weight = v.bit_count()
                if (residue-weight)%2:
                    continue
                value = ((residue-weight)//2) % (1<<bits)
                requirements = [v+1, *(var if value>>i&1 else -var for i,var in enumerate(row))]
                present = pool.id()
                f.extend([[-present,literal] for literal in requirements])
                f.append([present,*(-literal for literal in requirements)])
                occupancy.append(present)
            cap = max(0, 1+(length-residue)//modulus)
            if cap < len(occupancy):
                f.extend(CardEnc.atmost(occupancy,cap,vpool=pool,encoding=EncType.seqcounter).clauses)
    axis_edges = [[] for _ in range(dim)]
    for vertex,position in anchors:
        assert 0<=vertex<n and (position-vertex.bit_count())%2==0
        f.append([vertex+1])
        value=(position-vertex.bit_count())//2
        for i,literal in enumerate(phase[vertex]):
            f.append([literal if value>>i&1 else -literal])
    if anchor_distances:
        assert length < 2 << bits
        from q9_anchor_distances import add_distances
        add_distances(f,phase,[(0,0),(end,length),*anchors],length)
    if half_membership:
        midpoint=(length-1)//2
        anchors_by_position={pos:v for v,pos in anchors}
        from q9_half_membership import partition
        partition(f,phase,pool,(anchors_by_position[midpoint],anchors_by_position[midpoint+1]),midpoint)
    if prefix_cuts:
        assert anchor_distances and 0 < length < 2 << bits
        from q9_rank_prefix_cuts import add_prefix_cuts
        add_prefix_cuts(f, pool, phase, length, prefix_cuts)
    if axis_windows:
        assert anchor_distances and 0 < length < 2 << bits
        assert all(0<=start<stop<=length and 1<=minimum<=dim
                   for start,stop,minimum in axis_windows)
        from q9_rank_axis_windows import add_axis_windows
        add_axis_windows(f, pool, phase, axis_windows)
    incoming = [[] for _ in range(n)]
    outgoing = [[] for _ in range(n)]
    for u in range(n):
        for axis in range(dim):
            v=u | (1 << axis)
            if u==v:
                continue
            up,down=pool.id(),pool.id()
            axis_edges[axis].extend([up,down])
            f.extend([[-up,u+1],[-up,v+1],[-down,u+1],[-down,v+1],
                      [-u-1,-v-1,up,down],[-up,-down]])
            outgoing[u].append(up)
            incoming[v].append(up)
            outgoing[v].append(down)
            incoming[u].append(down)
            for x,y,z in zip(phase[u],phase[v],bump[v]):
                f.extend([[-up,-x,y],[-up,x,-y],[-down,-x,z],[-down,x,-z]])
    for v in range(n):
        if v != 0:
            f.append([-v-1,*incoming[v]])
        else:
            f.extend([[-a] for a in incoming[v]])
        if v != end:
            f.append([-v-1,*outgoing[v]])
        else:
            f.extend([[-a] for a in outgoing[v]])
    if pair17:
        assert (dim,length)==(9,221)
        add_pair_cuts(f,f.nv,minimum=17)
    if triple:
        assert not lex and len(triple)==3
        pool = IDPool(start_from=f.nv+1)
        for axis,count in enumerate(triple):
            f.extend(CardEnc.equals(axis_edges[axis],count,vpool=pool,encoding=EncType.cardnetwrk).clauses)
    if lex:
        add_endpoint_lex(f,dim,distance)
    return f,end


def check_cycle(c, dim, bits):
    assert len(c)==len(set(c)) and all(0<=v<1<<dim for v in c)
    vertices=set(c)
    assert len(parts(vertices,dim)) == 1 and all(deg(vertices,v,dim)==2 for v in vertices)
    assert len(c) % (2 << bits) == 0


def run(args):
    f,end=modular(args.dim,args.length,args.distance,args.bits,args.pair17,args.lex,args.census,args.triple)
    header=dict(dim=args.dim,length=args.length,distance=args.distance,bits=args.bits,
                budget=args.budget,variables=f.nv,clauses=len(f.clauses),pair17=args.pair17,lex=args.lex,census=args.census,triple=args.triple)
    print(json.dumps(dict(status="STARTED",**header)),flush=True)
    cuts=[]
    with Cadical195(bootstrap_with=f,with_proof=bool(args.proof)) as sat:
        while (remaining:=args.budget-sat.accum_stats()["conflicts"])>0:
            sat.conf_budget(remaining)
            answer=sat.solve_limited()
            if answer is None:
                break
            if answer is False:
                result=dict(status="UNSAT_solver")
                if args.proof:
                    stem,checker=args.proof
                    cnf,proof=Path(stem+".cnf"),Path(stem+".drat")
                    # Replay from the base instance plus individually validated cycle cuts.
                    f.to_file(str(cnf))
                    if cuts:
                        with Cadical195(bootstrap_with=f,with_proof=True) as replay:
                            if not replay.solve() is False:
                                raise AssertionError("cycle cuts did not reproduce UNSAT")
                            proof.write_text("\n".join(replay.get_proof())+"\n")
                    else:
                        proof.write_text("\n".join(sat.get_proof())+"\n")
                    check=subprocess.run([checker,str(cnf),str(proof)],capture_output=True,check=True)
                    assert b"s VERIFIED" in check.stdout
                    result.update(status="UNSAT_DRAT_verified",proof=str(proof))
                return dict(header,**result,cuts=cuts,**sat.accum_stats())
            model=sat.get_model()
            selected={v-1 for v in model if 1<=v<=1<<args.dim}
            cycles=[sorted(c) for c in parts(selected,args.dim) if 0 not in c]
            if not cycles:
                return dict(header,status="SAT_checked",
                            path=read_path(model,args.dim,args.length,end),**sat.accum_stats())
            for c in cycles:
                check_cycle(c,args.dim,args.bits)
                cl=[-v-1 for v in c]
                cuts.append(c)
                print(json.dumps(dict(status="CYCLE_CUT",length=len(c))),flush=True)
                f.append(cl)
                sat.add_clause(cl)
        return dict(header,status="UNKNOWN",cuts=cuts,**sat.accum_stats())


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    for field in ("dim","length","distance","bits","budget"):
        parser.add_argument(field,type=int)
    parser.add_argument("--pair17",action="store_true")
    parser.add_argument("--lex",action="store_true")
    parser.add_argument("--census",action="store_true")
    parser.add_argument("--triple",nargs=3,type=int)
    parser.add_argument("--proof",nargs=2)
    print(json.dumps(run(parser.parse_args())),flush=True)
