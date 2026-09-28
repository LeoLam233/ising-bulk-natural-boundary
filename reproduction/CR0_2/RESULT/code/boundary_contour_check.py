"""Numerical checks of the fixed-site continuation contour in RESULT section 7.
This does not evaluate or continue the full spatial susceptibility inside the circle.
Roots are followed continuously; selecting the small root after crossing would be wrong.
"""
from pathlib import Path
import json
import numpy as np
from log_action import log
root=Path(__file__).resolve().parents[1]

def roots(s,theta):
    t=s+1/s-np.cos(theta)
    z=np.sqrt(t*t-1+0j)
    return 1/(t+z),1/(t-z)

def tracked_q(zeta,eps,theta):
    q1,q2=roots(zeta*1.06,theta)
    q=np.where(np.abs(q1)<np.abs(q2),q1,q2)
    for e in np.linspace(.06,eps,101)[1:]:
        r1,r2=roots(zeta*(1+e),theta)
        q=np.where(np.abs(r1-q)<=np.abs(r2-q),r1,r2)
    return q

def determinant_value(s,theta,jac,q,M,N):
    b=2*q/(1-q*q)
    L=2*q[:,None]*np.sin((theta[:,None]-theta[None,:])/2)/(1-q[:,None]*q[None,:])
    weight=b*np.exp(1j*M*theta)*q**abs(N)*jac/len(theta)
    return np.linalg.det(np.eye(len(theta),dtype=complex)+L*weight[None,:])

def main():
    log('computation_start','RUN_OUTPUT/code/boundary_contour_check.py','Check deformed fixed-site contour, origin identity and continuous root tracking across one nonexceptional boundary point; no full susceptibility continuation claimed.')
    zeta=np.exp(2j*np.pi/7);eta=.16
    rows=[]
    for n in (192,384):
        t=-np.pi+2*np.pi*np.arange(n)/n
        theta=t+1j*eta*np.sin(t);jac=1+1j*eta*np.cos(t)
        for eps in (.03,0.,-.015):
            s=zeta*(1+eps);q=tracked_q(zeta,eps,theta)
            # In this particular local disk Re(1-s^-4)>0, so this is the
            # continuation of the exterior fourth root without a cut crossing.
            P=(1-s**(-4))**.25
            det0=determinant_value(s,theta,jac,q,0,0)
            corr11=P*determinant_value(s,theta,jac,q,1,1)
            rows.append({'nodes':n,'radial_offset':eps,'s':{'real':float(s.real),'imag':float(s.imag)},
                'P_times_origin_determinant':{'real':float((P*det0).real),'imag':float((P*det0).imag)},
                'origin_abs_error_from_one':float(abs(P*det0-1)),
                'fixed_site_1_1_correlation':{'real':float(corr11.real),'imag':float(corr11.imag)},
                'max_abs_tracked_q':float(np.max(np.abs(q))),
                'min_abs_pair_denominator_sampled':float(np.min(np.abs(1-q[:,None]*q[None,:])))})
    result={'classification':'Floating-point fixed-site check only. The analytic proof is section 7; no interval certification or infinite lattice sum is evaluated.',
            'boundary_point':'exp(2*pi*i/7)','eta':eta,'root_tracking_steps':100,'rows':rows}
    out=root/'evidence'/'boundary_contour_check.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    log('computation_complete','RUN_OUTPUT/code/boundary_contour_check.py',{'output':'RUN_OUTPUT/evidence/boundary_contour_check.json','status':'completed; full susceptibility not evaluated'})
if __name__=='__main__':main()
