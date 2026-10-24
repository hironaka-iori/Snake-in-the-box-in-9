"""Determine whether the endpoint-free lower bound eight is attained."""
from probe import solve,W
if __name__=='__main__':
    for cap in range(8,12):
        local=solve(f'first-radius-2-cap-{cap}',[W[2]],2,cap=cap,seconds=6)
        if local['status']=='SAT':
            solve(f'full-first-radius-2-cap-{cap}',[W[2]],2,ball_radius=9,cap=cap,seconds=20)
            break
