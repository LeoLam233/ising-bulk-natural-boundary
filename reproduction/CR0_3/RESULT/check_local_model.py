"""Finite diagnostics for the *localized* equal-angle saddle, not the full integral.
This script cannot certify that other regions or the infinite particle tail are smooth.
"""
from pathlib import Path
import json
import mpmath as mp
from record_action import record
mp.mp.dps=100
rows=[]
for p,j in [(7,1),(7,2),(11,1),(13,1)]:
    n=2*p
    theta=2*mp.pi*j/p
    st=mp.sin(theta); ct=mp.cos(theta)
    zeta=mp.exp(1j*theta)
    def gam(eps,u):
        s=zeta*(1+eps)
        Z=s+1/s-mp.cos(theta+u)
        d=mp.sqrt(Z*Z-1)
        if abs(-d-1j*st)<abs(d-1j*st):
            d=-d
        return mp.log(Z+d)
    deps=mp.diff(lambda e:gam(e,0),0)
    du=mp.diff(lambda u:gam(0,u),0)
    du2=mp.diff(lambda u:gam(0,u),0,2)
    h=mp.mpf(n*n)/2
    b=ct/(2*st)
    scale=mp.sqrt(abs(b)/n)
    # Equivalent reciprocal-radius integral. Split at the concentration scale.
    I=scale*abs(b)**(-h)*mp.quad(lambda v:(v*v-1j*mp.sign(b))**(-h),[0,1/mp.sqrt(h),1,mp.inf])
    exact=mp.mpf('0.5')/mp.sqrt(n)*(-1j*b)**(mp.mpf('0.5')-h)*mp.beta(mp.mpf('0.5'),h-mp.mpf('0.5'))
    relative=abs(I-exact)/abs(exact)
    deriv_error=max(abs(deps-2),abs(du+1j),abs(du2+2j*ct/st))
    ok=bool(relative<mp.mpf('1e-60') and deriv_error<mp.mpf('1e-80'))
    rows.append({'p':p,'root_index':j,'particle_n':n,'derivative_order_k':n*n//2-1,
                 'gamma_derivative_max_error':str(deriv_error),'radial_beta_relative_error':str(relative),
                 'radial_beta_integral_nonzero':bool(abs(exact)>0),'finite_diagnostic_pass':ok})
    assert ok
out={'kind':'floating_point_check_of_local_model_only','decimal_precision':mp.mp.dps,'rows':rows}
path=Path(__file__).resolve().parent/'local_model_checks.json'
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
record('compute','RUN_OUTPUT/check_local_model.py','Checked local gamma Taylor derivatives and nonzero radial beta integral at four prime-root saddles using 100-digit arithmetic. No global finite-integral or infinite-tail claim.','own_output')
