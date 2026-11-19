# Lower-bound search 2: snakepit annealing with cube surgery

Goal: a 192-edge snake in Q9, using the snakepit/cube-surgery annealing method
(arXiv:2607.15270, as summarised second-hand; the paper itself was not reachable
from this container).

Status: in progress. Calibration running. Best so far: 190 edges (validated by `src/check.py`).

- `src/surgery.c`: annealer (build: `gcc -O3 -march=native -o bin/surgery src/surgery.c -lm`).
- `src/check.py`: independent snake checker. `src/canon.py`: canonical forms, class counts.
- `src/portfolio.sh`: runs parameter portfolios on several cores.
- `logs/`: run logs (BEST lines carry full vertex lists).
