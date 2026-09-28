#!/usr/bin/env python3
"""Exact symbolic identities only; not certification of continuous estimates."""
import json
import sympy as s
x,z,X,Y,c,t=s.symbols('x z X Y c t')
D=(z+1/z-x-1/x)/2
res=s.simplify(s.limit((x-z)/D,x,z))
W=2*c-s.cos(t)
f2=s.diff(s.acos(W),t,2)
target=-2*c*((s.cos(t)-c)**2+1-c*c)/(1-W*W)**s.Rational(3,2)
A,bq,br,Ds=s.symbols('A bq br Ds')
xv=(Ds+bq*A)/(br-bq) # br denotes selected branch slope
Gq,Gr,Bq,Br=s.symbols('Gq Gr Bq Br')
den=Bq*Gr-Br*Gq
Vq, Vr=Ds*Gr/den,-Ds*Gq/den
n0=s.symbols('n0',integer=True,positive=True)
checks={
 'classification':'exact symbolic algebra; not a proof of analytic estimates, coverage or uniformity',
 'residue':str(res),
 'residue_equals_R':s.simplify(res-2*z*z/(1-z*z))==0,
 'offsite_factor_two':s.simplify((1+X)/(1-X)*(1+Y)/(1-Y)-1-2*(X+Y)/((1-X)*(1-Y)))==0,
 'compact_curvature':s.simplify(s.trigsimp(f2-target))==0,
 'all_B_sum_V_zero':s.simplify(A+A*br/(bq-br)-A*bq/(bq-br))==0,
 'all_B_residual_phase_zero':s.simplify(bq*A*br/(bq-br)-br*A*bq/(bq-br))==0,
 'mixed_sum_V_zero':s.simplify(A+xv-A-xv)==0,
 'mixed_phase_zero':s.simplify((br-bq)*xv-bq*A-Ds)==0,
 'coupled_Y_frozen':s.simplify(Gq*Vq+Gr*Vr)==0,
 'coupled_Z_frozen':s.simplify(Bq*Vq+Br*Vr-Ds)==0,
 'minimum_collision_power_L':str(s.expand((n0+2)**2-2*(n0*n0/2-1)-4)),
}
assert all(v for k,v in checks.items() if isinstance(v,bool))
print(json.dumps(checks,indent=2,ensure_ascii=False))
