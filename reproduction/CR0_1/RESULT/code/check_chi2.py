"""One-dimensional quadrature diagnostics for the two-particle integral.
The exact asymptotic and the failure of an absolute-integrand bound are proved
separately in RESULT.md. These quadratures are not certified interval bounds.
"""
from pathlib import Path
import json
import mpmath as mp
from log_action import log
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=65

def integrand(phi,s):
    z=s+1/s-mp.cos(phi)
    a=z+mp.sqrt(z*z-1); b=z-mp.sqrt(z*z-1)
    x=a if abs(a)<abs(b) else b
    y=2*x/(1-x*x)
    return mp.sin(phi)**2*z*y**5

def integral_real(u):
    s=mp.exp(u)
    panels=sorted(set([mp.mpf(0),u,10*u,mp.mpf('0.1'),mp.pi]))
    return mp.quad(lambda phi:integrand(phi,s),panels)/(2*mp.pi)

def integral_complex(u,theta):
    s=mp.exp(u+1j*theta); A=s+1/s
    edge=mp.acos(mp.re(A)-1)
    width=mp.im(A)/mp.sin(edge)
    panels=[mp.mpf(0),mp.pi]
    for scale in [-100,-10,-1,0,1,10,100]:
        v=edge+scale*width
        if 0<v<mp.pi: panels.append(v)
    panels=sorted(set(panels))
    signed=mp.quad(lambda phi:integrand(phi,s),panels)/(2*mp.pi)
    absolute=mp.quad(lambda phi:abs(integrand(phi,s)),panels)/(2*mp.pi)
    return signed,absolute

real=[]
for us in ['0.1','0.03','0.01','0.003','0.001','0.0001']:
    u=mp.mpf(us); F=integral_real(u)
    real.append({'u':us,'F2':mp.nstr(F,22),'u_squared_times_F2':mp.nstr(u*u*F,22),'ratio_to_limit':mp.nstr(u*u*F*12*mp.pi,22),'u_power_7over4_times_m2F2':mp.nstr(u**(mp.mpf(7)/4)*(1-mp.exp(-4*u))**mp.mpf('.25')*F,22)})
complex_rows=[]
for us in ['0.03','0.01','0.003','0.001','0.0003']:
    u=mp.mpf(us); signed,absolute=integral_complex(u,mp.pi/3)
    complex_rows.append({'u':us,'signed_F2':mp.nstr(signed,22),'absolute_integral':mp.nstr(absolute,22),'u_power_3over2_times_absolute':mp.nstr(u**mp.mpf('1.5')*absolute,22)})
out={'arithmetic':'mpmath 65-digit floating-point quadrature; no validated error enclosure','critical_limit_1over12pi':mp.nstr(1/(12*mp.pi),30),'critical_lower_amplitude_sqrt2over12pi':mp.nstr(mp.sqrt(2)/(12*mp.pi),30),'real_critical':real,'nonNickel_boundary_angle':'pi/3, s=exp(u+i*pi/3)','signed_vs_absolute':complex_rows}
(ROOT/'calculations'/'chi2_checks.json').write_text(json.dumps(out,indent=2)+'\n')
log('compute','RUN_OUTPUT/code/check_chi2.py',{'saved':'calculations/chi2_checks.json','real_samples':len(real),'complex_samples':len(complex_rows),'certification':'non-interval high-precision quadrature'})
print(json.dumps(out,indent=2))
