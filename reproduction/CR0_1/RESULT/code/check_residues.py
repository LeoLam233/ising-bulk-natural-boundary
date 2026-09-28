"""Exact local-residue/Jacobian checks and an absolute-integral constant.
No Ising tail is evaluated. Symbolic equalities use only rational functions.
"""
from pathlib import Path
import json
import sympy as sp
import mpmath as mp
from log_action import log
ROOT=Path(__file__).resolve().parents[1]
t,d,A,u,c,Q,rho=sp.symbols('t d A u c Q rho',nonzero=True)
center=4/((d-sp.I*t)*(A*u-d+sp.I*t-sp.I*c*Q))
res=sp.residue(center,t,-sp.I*d)
normalized=sp.simplify(-sp.I*res)
expected=4/(A*u-sp.I*c*Q)
assert sp.simplify(normalized-expected)==0
v=sp.Symbol('v')
inv_yD=-2/((v-rho)*(v-1/rho))
yres=sp.simplify(sp.residue(inv_yD,v,rho))
assert sp.simplify(yres-2*rho/(1-rho**2))==0
jacobians=[]
for n in [2,4,10,14]:
    J=sp.zeros(n)
    for j in range(n-1): J[j,j]=1; J[j,n-1]=sp.Rational(1,n)
    for j in range(n-1): J[n-1,j]=-1
    J[n-1,n-1]=sp.Rational(1,n)
    det=sp.det(J); assert det==1
    jacobians.append({'n':n,'determinant':str(det)})
mp.mp.dps=60
Cabs=2**(-mp.mpf(5)/2)/(2*mp.pi)*3**(-mp.mpf(3)/4)*mp.sqrt(mp.pi)*mp.gamma(mp.mpf(3)/4)/mp.gamma(mp.mpf(5)/4)
out={'exact_center_integral':str(normalized),'assumptions_center_integral':'A>0,u>0,0<d<A*u,c and Q real; contour closed below','exact_y_residue':str(yres),'jacobian_checks':jacobians,'absolute_F2_limit_at_theta_pi_over_3':mp.nstr(Cabs,35),'absolute_constant_status':'floating-point evaluation of analytically derived gamma-function constant'}
(ROOT/'calculations'/'residue_checks.json').write_text(json.dumps(out,indent=2)+'\n')
log('compute','RUN_OUTPUT/code/check_residues.py',{'saved':'calculations/residue_checks.json','arithmetic':'symbolic residues/Jacobians; floating evaluation of gamma constant'})
print(json.dumps(out,indent=2))
