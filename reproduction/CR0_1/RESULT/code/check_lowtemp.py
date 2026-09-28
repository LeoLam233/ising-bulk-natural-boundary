"""Exact low-temperature coefficients implied by the two-particle integral.
For q=1/s, F_4 starts at q^16, so the full X coefficients through q^14
are fixed by (1-q^4)^(1/4) F_2. No outside series is consulted.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial
import json
from log_action import log
ROOT=Path(__file__).resolve().parents[1]
MAX=14
coeff=[F(0) for _ in range(MAX+1)]
poch=F(1)
for k in range((MAX-4)//2+1):
    if k: poch*=F(2*k+3,2)/k
    r=4+2*k; base=4+2*k
    for j in range(MAX-base+1):
        for l in range(j+1):
            power=base+j+l; cpower=j-l
            if power>MAX or cpower%2: continue
            h=cpower//2
            moment=F(comb(2*h,h),4**(h+1)*(h+1))
            coeff[power]+=poch*comb(r+j-1,j)*comb(j,l)*(-1)**l*moment
mag=[F(0) for _ in range(MAX+1)]; mag[0]=F(1); b=F(1)
for t in range(1,MAX//4+1):
    b*=-(F(1,4)-(t-1))/t; mag[4*t]=b
full=[sum((coeff[j]*mag[i-j] for j in range(i+1)),F(0)) for i in range(MAX+1)]
rows=[]
for k in range(1,MAX//2+1):
    vcoeff=full[2*k]*4**k
    assert vcoeff.denominator==1
    rows.append({'q_power':2*k,'F2_coefficient':str(coeff[2*k]),'X_coefficient':str(full[2*k]),'v_power':k,'X_v_coefficient':int(vcoeff)})
assert all(coeff[k]==0 and full[k]==0 for k in range(1,MAX+1,2))
out={'arithmetic':'exact rational arithmetic','q':'1/s','v':'q^2/4','valid_full_series_through_q_power':MAX,'reason':'All even n>=4 begin at q^(n^2); general leading coefficient is 2^(-n(n-1)).','coefficients':rows}
(ROOT/'calculations'/'lowtemp_coefficients.json').write_text(json.dumps(out,indent=2)+'\n')
log('compute','RUN_OUTPUT/code/check_lowtemp.py',{'saved':'calculations/lowtemp_coefficients.json','arithmetic':'exact rational','full_series_through':'q^14'})
print(json.dumps(out,indent=2))
