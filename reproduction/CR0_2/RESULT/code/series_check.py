"""Exact rational low-temperature coefficients obtained from the derived S2 integral.
Variable u=1/s. Angular moments are exact: average cos(theta)^(2j)=C(2j,j)/4^j.
The proof in RESULT.md shows the p>=4 tail is O(u^16); hence degrees <16
of P(s)*S2(s) are also degrees <16 of the full normalized susceptibility.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import math
from log_action import log
LIMIT=10  # S2 has an external u^4; internal terms through u^10 suffice.
def mul(a,b):
    out={}
    for (u,c),x in a.items():
        for (v,d),y in b.items():
            if u+v<=LIMIT:
                key=(u+v,c+d)
                out[key]=out.get(key,F(0))+x*y
    return {k:v for k,v in out.items() if v}
def add_scaled(a,b,scale):
    out=dict(a)
    for k,v in b.items():out[k]=out.get(k,F(0))+scale*v
    return {k:v for k,v in out.items() if v}
def main():
    log('computation_start','RUN_OUTPUT/code/series_check.py','Exact Fraction arithmetic expansion of the derived two-particle integral; no numerical fitting.')
    z={(1,1):F(-2),(2,2):F(1),(2,0):F(1),(3,1):F(-2),(4,0):F(1)}
    power={(0,0):F(1)}; coeff=F(1);series={}
    for j in range(LIMIT+1):
        series=add_scaled(series,power,coeff)
        power=mul(power,z)
        coeff*= (F(-5,2)-j)/(j+1)
    series=mul(series,{(0,0):F(1),(1,1):F(-1),(2,0):F(1)})
    series=mul(series,{(0,0):F(1),(0,2):F(-1)})
    S2={}
    for (u,c),v in series.items():
        if c%2==0:
            moment=F(math.comb(c,c//2),4**(c//2))
            S2[u+4]=S2.get(u+4,F(0))+v*moment/2
    S2={k:v for k,v in sorted(S2.items()) if v}
    pref={0:F(1)};coeff=F(1)
    for j in range(1,4):
        coeff*= -(F(1,4)-(j-1))/j
        pref[4*j]=coeff
    X={}
    for i,a in S2.items():
        for j,b in pref.items():
            if i+j<16:X[i+j]=X.get(i+j,F(0))+a*b
    X={k:v for k,v in sorted(X.items()) if v}
    assert S2[4]==F(1,4) and X[4]==F(1,4)
    assert all(k%2==0 for k in X)
    result={'classification':'Exact finite coefficients from an algebraic expansion and exact angular moments. The O(u^16) tail statement relies on the analytical estimate in RESULT.md, not finite coefficient evidence alone.',
        'variable':'u=1/s','S2_coefficients_below_degree_16':{str(k):str(v) for k,v in S2.items()},
        'full_X_coefficients_below_degree_16':{str(k):str(v) for k,v in X.items()}}
    out=Path(__file__).resolve().parents[1]/'evidence'/'exact_series.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    log('computation_complete','RUN_OUTPUT/code/series_check.py',{'output':'RUN_OUTPUT/evidence/exact_series.json','status':'exact coefficient calculation completed'})
if __name__=='__main__':main()
