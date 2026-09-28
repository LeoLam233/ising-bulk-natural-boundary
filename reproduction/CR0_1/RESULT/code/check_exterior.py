"""High-precision diagnostics for the analytic argument; NOT interval certification.
No data or algorithms are loaded outside the supplied packet and installed runtime.
"""
from pathlib import Path
import json, math
import mpmath as mp
from log_action import log
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=90

def inner_root(s, phi):
    z=s+1/s-mp.cos(phi)
    a=z+mp.sqrt(z*z-1); b=z-mp.sqrt(z*z-1)
    x=a if abs(a)<abs(b) else b
    if not abs(x)<1:
        raise ArithmeticError('outside branch')
    return x

def h_matrix(s, angles):
    xs=[inner_root(s,t) for t in angles]
    # Principal square roots are consistent for the chosen samples. Any sign
    # change conjugates the antisymmetric matrix by a diagonal sign matrix.
    return mp.matrix([[0 if i==j else 2*mp.sin((angles[i]-angles[j])/2)*mp.sqrt(xs[i])*mp.sqrt(xs[j])/(1-xs[i]*xs[j])
                       for j in range(len(xs))] for i in range(len(xs))])

rows=[]
for s in [mp.mpf('2'),mp.mpc('1.1','0.7'),mp.mpc('-1.4','0.3'),mp.mpc('0.2','1.3')]:
    for n in [2,4,6,8]:
        angles=[mp.mpf(-2)+mp.mpf(4)*(j+mp.mpf('0.17'))/n+mp.mpf('0.03')*j*j/n/n for j in range(n)]
        h=h_matrix(s,angles); det=mp.det(h)
        prod=mp.fprod(h[i,j]**2 for i in range(n) for j in range(i+1,n))
        rel=abs(det-prod)/abs(prod)
        bound=n**(mp.mpf(n)/2)*(max(abs(v) for v in h))**n
        rows.append({'s':str(s),'n':n,'relative_identity_error':mp.nstr(rel,12),'determinant_abs':mp.nstr(abs(det),12),'hadamard_upper':mp.nstr(bound,12)})

ellipse=[]
for r in [mp.mpf('1.01'),mp.mpf('1.2'),mp.mpf('2'),mp.mpf('5')]:
    max_ratio=mp.mpf(0); arg=None
    for k in range(48):
        s=r*mp.exp(2j*mp.pi*(k+mp.mpf('0.21'))/48)
        for j in range(48):
            phi=2*mp.pi*j/48
            ratio=abs(inner_root(s,phi))*r
            if ratio>max_ratio: max_ratio=ratio; arg=[k,j]
    ellipse.append({'r':str(r),'max_sampled_r_times_abs_x':mp.nstr(max_ratio,18),'grid':[48,48],'max_grid_indices':arg})

tails=[]
# The tail formula is proved symbolically in RESULT.md. These are approximate
# evaluations of that proved upper bound, not certified rounding intervals.
for r in ['1.5','2','3']:
    r=mp.mpf(r); H=2*r/(r*r-1); R2=(1+r**-2)/(1-r**-2)
    N=2*math.ceil(max(10,2*mp.e*H**4)/2)
    a=mp.mpf(N)**(mp.mpf(N)/2)*H**(2*N)/mp.factorial(N)
    rho=mp.e*H**4/(N+1)
    tails.append({'r':str(r),'H':mp.nstr(H,18),'even_start_N':N,'ratio_bound':mp.nstr(rho,18),'tail_upper_bound_approx':mp.nstr(R2*a/(1-rho),18)})

out={'arithmetic':'mpmath floating point, 90 decimal digits; not rigorous interval arithmetic','mpmath_version':mp.__version__, 'determinant_identity':rows,'ellipse_root_samples':ellipse,'tail_bound_evaluations':tails}
p=ROOT/'calculations'/'exterior_checks.json'; p.write_text(json.dumps(out,indent=2)+'\n')
log('compute','RUN_OUTPUT/code/check_exterior.py',{'saved':'calculations/exterior_checks.json','checks':len(rows),'max_relative_identity_error':mp.nstr(max(mp.mpf(row['relative_identity_error']) for row in rows),12),'sampled_roots':len(ellipse)*48*48,'certification':'floating point diagnostics only','mpmath_version':mp.__version__})
print(json.dumps(out,indent=2))
