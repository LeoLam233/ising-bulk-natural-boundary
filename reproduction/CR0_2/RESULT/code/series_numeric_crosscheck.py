"""Compare the exact finite series with independently integrated S2 at large s."""
from pathlib import Path
import json
from fractions import Fraction
import mpmath as mp
from self_checks import S2_real
from log_action import log
root=Path(__file__).resolve().parents[1]
log('computation_start','RUN_OUTPUT/code/series_numeric_crosscheck.py','Cross-check rational series against independent high-precision quadrature; finite-order error only.')
data=json.loads((root/'evidence'/'exact_series.json').read_text())
coef={int(k):Fraction(v) for k,v in data['S2_coefficients_below_degree_16'].items()}
rows=[]
for ss in ('4','8','16','32'):
    s=mp.mpf(ss);u=1/s
    approx=sum(mp.mpf(v.numerator)/v.denominator*u**k for k,v in coef.items())
    a=s+1/s
    def f(t):
        z=a-mp.cos(t)
        return mp.sin(t)**2*z/(z*z-1)**mp.mpf('2.5')
    exact=mp.quad(f,[0,mp.pi])/(2*mp.pi)
    rows.append({'s':ss,'truncated_S2':mp.nstr(approx,35),'quadrature_S2':mp.nstr(exact,35),'error':mp.nstr(exact-approx,20),'error_divided_by_u16':mp.nstr((exact-approx)/u**16,20)})
result={'classification':'Non-rigorous independent quadrature cross-check of an exact formal calculation. No boundary conclusion follows.','rows':rows}
(root/'evidence'/'series_numeric_crosscheck.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
log('computation_complete','RUN_OUTPUT/code/series_numeric_crosscheck.py',{'output':'RUN_OUTPUT/evidence/series_numeric_crosscheck.json','status':'completed'})
