"""Evaluate the exact polynomial construction in the report at finite points.
These floating-point values are illustrative; the telescoping identity and compact
convergence of the construction are proved analytically in the report.
"""
from pathlib import Path
import json
import mpmath as mp
from record_action import record
mp.mp.dps=100

def Q(n,z):
    L=n*n; K=n**4
    term=mp.mpf(1); acc=term
    for j in range(1,L):
        term *= (K+j-1)*(1-z)/j
        acc += term
    return z**K*acc
rows=[]
for z in [mp.mpf('0.5'),mp.mpf('0.9'),mp.mpf('0.99'),mp.mpf('0.9999'),mp.mpc('0.5','0.3')]:
    for n in [1,2,4,8,16]:
        q=Q(n,z)
        rows.append({'z':str(z),'n':n,'Q_n':str(q),'absolute_partial_sum_alpha_half':str(abs(mp.sqrt(1-z)*q))})
result={'kind':'illustration_not_interval_certification','decimal_precision':mp.mp.dps,'rows':rows}
path=Path(__file__).resolve().parent/'cancellation_checks.json'
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
record('compute','RUN_OUTPUT/check_cancellation.py','Evaluated 25 finite instances of the explicit analytic telescoping counterexample; saved cancellation_checks.json. Illustrative floating-point output only.','own_output')
