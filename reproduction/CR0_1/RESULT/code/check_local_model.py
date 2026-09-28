"""Check the local prime-root saddle normal form against the BG integrand.
These are finite floating-point diagnostics, not high-dimensional integration
or a proof of summability of the full susceptibility at its boundary.
"""
from pathlib import Path
import json
import mpmath as mp
from log_action import log
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=95

def xy(s,phi):
    z=s+1/s-mp.cos(phi); d=mp.sqrt(z*z-1)
    x=min([z+d,z-d],key=abs)
    return x,2*x/(1-x*x)

def integrand(s,angles):
    xyv=[xy(s,a) for a in angles]; xs=[r[0] for r in xyv]
    P=mp.fprod(xs); amp=mp.fprod(r[1] for r in xyv)
    for j in range(len(xs)):
        for k in range(j+1,len(xs)):
            amp*=4*mp.sin((angles[j]-angles[k])/2)**2*xs[j]*xs[k]/(1-xs[j]*xs[k])**2
    return amp*(1+P)/(1-P)

samples=[]
for p,a in [(5,1),(5,2),(7,1),(7,3)]:
    n=2*p; theta=2*mp.pi*a/p; c=mp.cot(theta)
    base=[mp.mpf(j)-(n-1)/mp.mpf(2) for j in range(n)]
    norm=mp.sqrt(mp.fsum(b*b for b in base)); base=[b/norm for b in base]
    for us in ['0.01','0.001','0.0001','0.00001']:
        u=mp.mpf(us); v=[mp.sqrt(u)*b for b in base]
        Q=mp.fsum(t*t for t in v)
        delta2=mp.fprod((v[j]-v[k])**2 for j in range(n) for k in range(j+1,n))
        leading=2*delta2/(2**(n*(n-1))*mp.sin(theta)**(n*n)*(2*n*u-1j*c*Q))
        s=mp.exp(u+1j*theta)
        ratios=[]
        for sign in [-1,1]:
            exact=integrand(s,[sign*theta+t for t in v])
            ratios.append(mp.nstr(exact/leading,20))
        samples.append({'p':p,'a':a,'n':n,'u':us,'negative_phi_saddle_ratio':ratios[0],'positive_phi_saddle_ratio':ratios[1]})

radial=[]
for p,a in [(5,1),(5,2),(7,1),(7,3)]:
    n=2*p; theta=2*mp.pi*a/p; c=mp.cot(theta); A=2*n
    k=n*n//2-1; nu=mp.mpf(n*n-1)/2
    predicted=mp.mpf('.5')*A**mp.mpf('-.5')*(-1j*c)**(-nu)*mp.beta(nu,mp.mpf('.5'))
    f=lambda r:r**(n*n-2)/(A-1j*c*r*r)**(k+1)
    numeric=mp.quad(f,[0,1,3,10,30,100,mp.inf])
    radial.append({'p':p,'a':a,'n':n,'derivative_k':k,'nu':str(nu),'predicted_radial_integral':mp.nstr(predicted,22),'relative_quadrature_error':mp.nstr(abs((numeric-predicted)/predicted),12)})
out={'arithmetic':'95-digit mpmath floating point; no rigorous error enclosures','scope':'local Taylor normal form and one-dimensional radial beta integral only; not full F_n or infinite-tail evaluation','local_integrand_ratios':samples,'radial_beta_checks':radial}
(ROOT/'calculations'/'local_model_checks.json').write_text(json.dumps(out,indent=2)+'\n')
log('compute','RUN_OUTPUT/code/check_local_model.py',{'saved':'calculations/local_model_checks.json','local_samples':len(samples),'radial_samples':len(radial),'certification':'floating-point diagnostics only'})
print(json.dumps(out,indent=2))
