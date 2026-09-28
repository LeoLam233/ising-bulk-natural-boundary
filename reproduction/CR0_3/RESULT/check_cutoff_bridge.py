"""Double-precision periodic quadrature checking the independently normalized
n=2 residue/Abel bridge A_2 = O_2 + 2 U_2. This is not an interval proof.
"""
from pathlib import Path
import json
import numpy as np
from record_action import record

def root(z):
    d=np.sqrt(z*z-1+0j)
    plus=z+d; minus=z-d
    big=np.where(np.abs(plus)>=np.abs(minus),plus,minus)
    return 1/big

def xy(s,x):
    q=root(s+1/s-(x+1/x)/2)
    y=2*q/(1-q*q)
    return q,y

def enc(z):
    return {'real':float(np.real(z)),'imag':float(np.imag(z))}

rows=[]
s=2.0
for L in [128,256,512]:
    theta=2*np.pi*np.arange(L)/L
    xu=np.exp(1j*theta)
    q,y=xy(s,xu)
    A=.5*np.mean((y*y)*(1+q*q)/(1-q*q)*(4*np.sin(theta)**2*q*q/(1-q*q)**2))
    def S(x,q,y):
        X=x[:,None]; Y=x[None,:]
        QQ=q[:,None]*q[None,:]
        h2=-(X-Y)**2/(X*Y)*QQ/(1-QQ)**2
        return h2*y[:,None]*y[None,:],X*Y,QQ
    Su,_,_=S(xu,q,y)
    O=.5*np.mean(Su)
    for r in [.6,.75,.9,.96]:
        x=r*xu
        qr,yr=xy(s,x)
        Sr,P,Q=S(x,qr,yr)
        U=.5*np.mean(Sr*(P+Q)/((1-P)*(1-Q)))
        err=abs(O+2*U-A)
        rows.append({'grid_per_angle':L,'contour_radius':r,'A2':enc(A),'O2':enc(O),'U2':enc(U),
                     'absolute_bridge_discrepancy':float(err),'max_y_pole_modulus':float(np.max(np.abs(qr))),
                     'poles_inside_contour':bool(np.max(np.abs(qr))<r)})
assert max(r['absolute_bridge_discrepancy'] for r in rows if r['grid_per_angle']==512)<1e-11
result={'kind':'floating_point_diagnostic_not_proof','numpy_version':np.__version__,
        'convention':'one factor 1/(2*pi*i) per contour variable; n! division','rows':rows}
path=Path(__file__).resolve().parent/'cutoff_bridge_checks.json'
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
record('compute','RUN_OUTPUT/check_cutoff_bridge.py','Checked the n=2 residue/Abel normalization at three periodic grid sizes and four contour radii; saved cutoff_bridge_checks.json. Double-precision diagnostic, not interval certification.','own_output')
