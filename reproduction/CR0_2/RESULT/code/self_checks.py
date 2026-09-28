"""Independent finite checks of formulas used in RESULT.md (not a proof of the boundary claim).
Only installed numpy/mpmath and Python standard library are used. No network or external data.
"""
from pathlib import Path
import json
import math
import platform
import sys
import numpy as np
import mpmath as mp
from log_action import log
OUT=Path(__file__).resolve().parents[1]/'evidence'
mp.mp.dps=65

def q_mp(s, theta):
    t=s+1/s-mp.cos(theta)
    z=mp.sqrt(t*t-1)
    # Exactly one root has modulus <1 off the cut. Select the larger denominator
    # to avoid cancellation in t - sqrt(t*t - 1) at large t.
    den=t+z if abs(t+z)>abs(t-z) else t-z
    return 1/den

def q_np(s, theta):
    t=complex(s)+1/complex(s)-np.cos(theta)
    z=np.sqrt(t*t-1+0j)
    den=np.where(np.abs(t+z)>np.abs(t-z),t+z,t-z)
    return 1/den

def str_mp(v):
    return {'real':mp.nstr(mp.re(v),40),'imag':mp.nstr(mp.im(v),40)}

def determinant_checks():
    rows=[]
    for s0 in [('real',mp.mpf('1.7')),('complex',mp.mpc('1.4','0.6')),('negative',mp.mpf('-1.7'))]:
        label,s=s0
        for n in (2,4,6,8):
            # Deterministic distinct angles, not a random unrecorded seed.
            theta=[-mp.pi+2*mp.pi*(mp.mpf(j)+mp.mpf('0.17')+mp.mpf('0.023')*j*j)/(n+1) for j in range(n)]
            q=[q_mp(s,t) for t in theta]
            A=mp.matrix(n,n)
            prod=mp.mpf(1)
            for i in range(n):
                for j in range(n):
                    A[i,j]=2*q[i]*mp.sin((theta[i]-theta[j])/2)/(1-q[i]*q[j])
                for j in range(i+1,n):
                    prod*=4*q[i]*q[j]*mp.sin((theta[i]-theta[j])/2)**2/(1-q[i]*q[j])**2
            det=mp.det(A)
            rel=abs(det-prod)/max(abs(det),abs(prod),mp.mpf('1e-150'))
            rows.append({'s_label':label,'s':str_mp(s),'particles':n,'determinant':str_mp(det),'pair_product':str_mp(prod),'relative_difference':mp.nstr(rel,12)})
            if rel>mp.mpf('1e-35'):
                raise AssertionError(('determinant identity',label,n,rel))
    return rows

def origin_nystrom():
    rows=[]
    for s in (2.0,1.3,1.08,1.4+0.6j,-1.7):
        # This is numerical Nyström quadrature, not an interval bound.
        expected=(1-complex(s)**(-4))**(-0.25)
        for size in (24,48,96):
            th=-np.pi+2*np.pi*np.arange(size)/size
            q=q_np(s,th)
            b=2*q/(1-q*q)
            A=2*q[:,None]*np.sin((th[:,None]-th[None,:])/2)/(1-q[:,None]*q[None,:])
            value=np.linalg.det(np.eye(size,dtype=complex)+A*b[None,:]/size)
            rows.append({'s':{'real':complex(s).real,'imag':complex(s).imag},'nodes':size,'det_I_plus_K':{'real':float(value.real),'imag':float(value.imag)},'expected_inverse_m_squared':{'real':expected.real,'imag':expected.imag},'abs_error':abs(value-expected)})
    return rows

def contour_checks():
    rows=[]
    s=1.6+0.4j
    size=160
    for M,N in ((0,0),(1,2),(3,1)):
        values=[]
        for shift in (0.,0.04,0.08):
            th=(-np.pi+2*np.pi*np.arange(size)/size)+1j*shift
            q=q_np(s,th)
            if np.max(np.abs(q))>=1:
                raise AssertionError('Chosen diagnostic contour left small-root sheet')
            b=2*q/(1-q*q)
            Q=q[:,None]*q[None,:]
            h2=4*Q*np.sin((th[:,None]-th[None,:])/2)**2/(1-Q)**2
            summand=h2*b[:,None]*b[None,:]*np.exp(1j*M*(th[:,None]+th[None,:]))*Q**N
            val=np.mean(summand)/2
            values.append(val)
            rows.append({'s':{'real':s.real,'imag':s.imag},'M':M,'N':N,'nodes_per_angle':size,'imaginary_shift':shift,'value':{'real':float(val.real),'imag':float(val.imag)},'max_abs_q_sampled':float(np.max(np.abs(q))),'abs_change_from_unshifted':float(abs(val-values[0]))})
        if max(abs(v-values[0]) for v in values)>1e-13:
            raise AssertionError('Contour diagnostic inconsistent')
    return rows

def S2_real(s):
    d=(s-1)**2/s
    # Rescale theta via sin(theta/2)=sqrt(d/2)*u. Integrate on separated scales.
    U=mp.sqrt(2/d)
    def integrand(u):
        if u>=U:
            return mp.mpf(0)
        return (u*u*mp.sqrt(1-d*u*u/2)*(1+d+d*u*u)
                /((1+u*u)**mp.mpf('2.5')*(2+d+d*u*u)**mp.mpf('2.5')))
    cuts=[mp.mpf(0)]+[v for v in map(mp.mpf,('1','4','16','64','256','1024','4096')) if v<U]+[U]
    return 4/(mp.pi*2**mp.mpf('1.5')*d)*mp.quad(integrand,cuts)

def critical_checks():
    rows=[]
    for estr in ('0.3','0.1','0.03','0.01','0.003','0.001','0.00001'):
        eps=mp.mpf(estr);s=1+eps;d=eps**2/s
        val=S2_real(s);m2=(1-s**(-4))**mp.mpf('.25')
        rows.append({'s_minus_one':estr,'S2':mp.nstr(val,35),'12_pi_d_S2':mp.nstr(12*mp.pi*d*val,35),'m_squared_S2_times_eps_7_over_4':mp.nstr(m2*val*eps**mp.mpf('1.75'),35)})
    return {'predicted_limits':{'12_pi_d_S2':'1','weighted_limit':mp.nstr(mp.sqrt(2)/(12*mp.pi),35)},'values':rows}

def main():
    log('computation_start','RUN_OUTPUT/code/self_checks.py','Finite determinant identities, origin normalization, contour-shift and critical-asymptotic diagnostics; floating-point only.')
    result={'classification':'Non-rigorous finite numerical diagnostics; all mathematical conclusions require the analytical proofs in RESULT.md.',
            'versions':{'python':sys.version,'numpy':np.__version__,'mpmath':mp.__version__},
            'mpmath_decimal_digits':mp.mp.dps,'determinant_identity':determinant_checks(),
            'origin_nystrom':origin_nystrom(),'contour_shift':contour_checks(),'critical_two_particle':critical_checks()}
    path=OUT/'self_checks.json'
    path.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    summary={'status':'diagnostics_completed','determinant_max_relative_difference':max(float(r['relative_difference']) for r in result['determinant_identity']),
             'origin_errors_at_96_nodes':[{'s':r['s'],'abs_error':r['abs_error']} for r in result['origin_nystrom'] if r['nodes']==96],
             'contour_max_abs_change':max(r['abs_change_from_unshifted'] for r in result['contour_shift']),
             'critical_two_particle':result['critical_two_particle']}
    print(json.dumps(summary,indent=2,ensure_ascii=False))
    log('computation_complete','RUN_OUTPUT/code/self_checks.py',{'output':'RUN_OUTPUT/evidence/self_checks.json','status':'completed; no interval certification','summary':summary})
if __name__=='__main__':
    main()
