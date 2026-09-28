"""Exact finite checks: low-temperature coefficients, prime-root pairs, and
boundary-flat polynomials used in an abstract cancellation counterexample.
All arithmetic in these checks is rational/integer or symbolic polynomial arithmetic.
"""
from pathlib import Path
import json
import math
import sympy as sp
from record_action import record

t,c=sp.symbols('t c')
A=1-c*t+t*t
U=sp.expand(A*A-t*t-1)
order=11
P=sp.Integer(1)
Up=sp.Integer(1)
for j in range(1,order):
    Up=sp.series(Up*U,t,0,order).removeO().expand()
    P += sp.binomial(sp.Rational(-5,2),j)*Up
P=sp.series(A*(1-c*c)*P,t,0,order).removeO().expand()
def circle_average(poly):
    ans=0
    for (k,),coeff in sp.Poly(poly,c).terms():
        if k%2==0:
            ans += coeff*sp.binomial(k,k//2)/4**(k//2)
    return sp.simplify(ans)
T2=sp.expand(t**4/2 * sum(circle_average(P.coeff(t,j))*t**j for j in range(order)))
X=sp.series((1-t**4)**sp.Rational(1,4)*T2,t,0,16).removeO().expand()
series_rows=[{'power_t':j,'T2_coefficient':str(T2.coeff(t,j)),
              'full_X_coefficient_below_t16':str(X.coeff(t,j))} for j in range(4,16) if X.coeff(t,j)!=0 or T2.coeff(t,j)!=0]

pair_rows=[]
for p in [7,11,13,17,19]:
    def vec(j):
        r=(j*((p+1)//2))%p
        sg=1 if j%2==0 else -1
        v=[0]*p
        v[r]+=sg
        v[(-r)%p]+=sg
        return v
    vv=[vec(j) for j in range(2*p)]
    for k in range(1,p):
        target=vv[2*k]
        actual=[]
        for a in range(2*p):
            for b in range(2*p):
                coeff=[vv[a][h]+vv[b][h]-2*target[h] for h in range(p)]
                if len(set(coeff))==1: # multiple of Phi_p=1+z+...+z^(p-1)
                    actual.append((a,b))
        expected=sorted((a,b) for a in [2*k,2*p-2*k] for b in [2*k,2*p-2*k])
        ok=sorted(actual)==expected
        pair_rows.append({'p':p,'k':k,'number_of_ordered_solutions':len(actual),'only_equal_real_parts':ok})
        assert ok

jet_rows=[]
for n in range(1,7):
    L=n*n
    K=n**4
    # Q_n(1-x)=(1-x)^K sum_{j=0}^{L-1} binomial(K+j-1,j)x^j.
    # Compute only the required finite jet, avoiding huge full polynomials.
    jet=[]
    for h in range(L+1):
        val=sum((-1)**(h-j)*math.comb(K,h-j)*math.comb(K+j-1,j)
                for j in range(min(h,L-1)+1) if h-j<=K)
        jet.append(val)
    assert jet[0]==1 and all(v==0 for v in jet[1:L])
    assert jet[L]==-math.comb(K+L-1,L)
    jet_rows.append({'n':n,'L':L,'K':K,'jet_degrees_1_through_L_minus_1_zero':True,
                     'coefficient_at_L':str(jet[L])})
result={'kind':'exact_finite_arithmetic_checks_not_a_universal_proof','sympy_version':sp.__version__,
        'series':series_rows,'prime_pair_checks':pair_rows,'boundary_flat_jet_checks':jet_rows}
out=Path(__file__).resolve().parent/'exact_checks.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
record('compute','RUN_OUTPUT/check_exact.py','Computed exact coefficients through t^14, exact minimal-order prime-root pair tests for p=7,11,13,17,19, and six exact flat-polynomial jets; saved exact_checks.json.','own_output')
