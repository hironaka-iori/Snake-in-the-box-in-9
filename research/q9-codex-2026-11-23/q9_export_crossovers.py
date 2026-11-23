from q9_crossover_projection import generate
import sys
cases,w,stats=generate('/tmp/q9_project_records_input9',120000)
assert w is None
for quality,q,h,cut in cases:
    print(' '.join(str(v+128*c) for v,colors in zip(q,h) for c in colors))
