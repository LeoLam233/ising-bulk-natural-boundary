"""High-precision diagnostics for the explicitly reduced two-particle integral.
Not an interval proof; the asymptotic proof is in RESULT.md.
"""
from pathlib import Path
import json
import mpmath as mp
from record_action import record
mp.mp.dps=85

def two_particle_real(s):
    if not s>1:
        raise ValueError('This numerical routine is restricted to real s>1.')
    mu=(s-1)**2/s
    def f(phi):
        d=mu+2*mp.sin(phi/2)**2
        return (1+d)*mp.sin(phi)**2/(d*(2+d))**mp.mpf('2.5')
    scale=mp.sqrt(2*mu)
    pts=sorted(set([mp.mpf(0),mp.pi]+[scale*x for x in [1,10,100] if scale*x<mp.pi]+[mp.mpf('0.1')]))
    return mp.quad(f,pts)/(2*mp.pi)

rows=[]
for j in [1,2,3,4,6,8,10,12]:
    eps=mp.mpf(10)**(-j)
    s=1+eps
    mu=eps**2/s
    val=two_particle_real(s)
    m2=(-mp.expm1(-4*mp.log(s)))**mp.mpf('0.25')
    rows.append({'epsilon':str(eps),'T2':str(val),'mu_times_T2':str(mu*val),
                 'ratio_to_1_over_12pi':str(12*mp.pi*mu*val),
                 'scaled_positive_lower_bound':str(eps**mp.mpf('1.75')*m2*val)})
result={'kind':'floating_point_diagnostic_not_rigorous_interval_bound', 'precision_decimal_digits':mp.mp.dps,
        'predicted_mu_T2_limit':str(1/(12*mp.pi)),
        'predicted_scaled_lower_bound_limit':str(mp.sqrt(2)/(12*mp.pi)), 'rows':rows}
out=Path(__file__).resolve().parent/'two_particle_checks.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
record('compute','RUN_OUTPUT/check_two_particle.py','Executed eight 85-digit quadratures approaching s=1; saved two_particle_checks.json. Floating-point diagnostics, not proof.','own_output')
