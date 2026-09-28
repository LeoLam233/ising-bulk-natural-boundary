"""Refine the near-critical quadrature diagnostic, preserving initial outputs."""
from pathlib import Path
import json
import numpy as np
import mpmath as mp
from self_checks import q_np, S2_real
from log_action import log

def main():
    log('computation_start','RUN_OUTPUT/code/refine_checks.py','Refine origin quadrature near criticality and compare two distinct 1D parametrizations of S2; initial outputs preserved.')
    rows=[]
    s=1.08
    expected=(1-s**(-4))**(-.25)
    for n in (96,192,384):
        th=-np.pi+2*np.pi*np.arange(n)/n
        q=q_np(s,th);b=2*q/(1-q*q)
        A=2*q[:,None]*np.sin((th[:,None]-th[None,:])/2)/(1-q[:,None]*q[None,:])
        v=np.linalg.det(np.eye(n,dtype=complex)+A*b[None,:]/n)
        rows.append({'s':s,'nodes':n,'value_real':float(v.real),'value_imag':float(v.imag),'expected':expected,'abs_error':float(abs(v-expected))})
    checks=[]
    for ss in ('1.3','1.1','1.01'):
        s=mp.mpf(ss);a=s+1/s;d=(s-1)**2/s
        def integrand(theta):
            t=a-mp.cos(theta)
            return mp.sin(theta)**2*t/(t*t-1)**mp.mpf('2.5')
        cuts=[mp.mpf(0),mp.sqrt(d),mp.sqrt(2*d),mp.mpf('.5'),mp.pi]
        cuts=sorted(set(cuts))
        theta_integral=mp.quad(integrand,cuts)/(2*mp.pi)
        scaled=S2_real(s)
        checks.append({'s':ss,'theta_integral':mp.nstr(theta_integral,35),'scaled_u_integral':mp.nstr(scaled,35),'abs_difference':mp.nstr(abs(theta_integral-scaled),12)})
    result={'classification':'Floating-point convergence checks only; no interval certification.',
            'origin_refinement':rows,'independent_S2_parametrizations':checks,
            'initial_roundoff_note':'Initial scaled-u quadrature occasionally returned imaginary residuals around 1e-101 at a square-root endpoint. Initial data were not overwritten; the intended integral is real and these residuals are numerical, not physical.'}
    out=Path(__file__).resolve().parents[1]/'evidence'/'refined_checks.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    log('computation_complete','RUN_OUTPUT/code/refine_checks.py',{'output':'RUN_OUTPUT/evidence/refined_checks.json','largest_node_origin_error':rows[-1]['abs_error'],'status':'completed; initial output retained'})
if __name__=='__main__':
    main()
