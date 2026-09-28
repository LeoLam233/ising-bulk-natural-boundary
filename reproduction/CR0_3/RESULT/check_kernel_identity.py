"""Finite, non-certified high-precision checks of branch and determinant formulas.
Only locally installed mpmath; all test data are generated here deterministically.
"""
from pathlib import Path
import json
import mpmath as mp
from record_action import record
mp.mp.dps = 90

def small_root(z):
    d = mp.sqrt(z*z-1)
    # Use reciprocal form to avoid subtraction when the large root is chosen.
    big = z+d if abs(z+d) >= abs(z-d) else z-d
    return 1/big

def enc(v):
    if isinstance(v, (mp.mpf, mp.mpc)):
        return str(v)
    raise TypeError(type(v).__name__)

rows=[]
for s in [mp.mpf('2'), mp.mpc('1.2','0.4'),mp.mpf('-2'),mp.mpc(0,2)]:
    for n in [2,4,6,8]:
        angles=[mp.pi*mp.mpf(((17*j+5)%43)-21)/23 for j in range(n-1)]
        angles.append(-sum(angles))
        roots=[small_root(s+1/s-mp.cos(t)) for t in angles]
        H=mp.matrix(n)
        product=mp.mpf(1)
        for i in range(n):
            for j in range(i+1,n):
                h=2*mp.sin((angles[i]-angles[j])/2)*mp.sqrt(roots[i])*mp.sqrt(roots[j])/(1-roots[i]*roots[j])
                H[i,j]=h
                H[j,i]=-h
                product *= h*h
        det=mp.det(H)
        rel=abs(det-product)/max(abs(det),abs(product),mp.mpf('1e-80'))
        q=max(map(abs,roots))
        bound=(mp.sqrt(n)*2*q/(1-q*q))**n
        rows.append(dict(s=s,n=n,max_root_modulus=q,inverse_s_modulus=1/abs(s),inverse_modulus_bound_pass=bool(q<1/abs(s)),root_residual=max(abs(x+1/x-2*(s+1/s-mp.cos(t))) for x,t in zip(roots,angles)),
                         determinant=det,product=product,relative_discrepancy=rel,hadamard_bound=bound,
                         finite_check_pass=bool(rel < mp.mpf('1e-45') and q<1/abs(s) and abs(det)<=bound)))
result={'kind':'floating_point_diagnostic_not_proof','mpmath_version':mp.__version__,'decimal_precision':mp.mp.dps,'tests':rows}
out=Path(__file__).resolve().parent/'kernel_identity_checks.json'
out.write_text(json.dumps(result,default=enc,indent=2)+'\n')
print(json.dumps(result,default=enc,indent=2))
record('compute','RUN_OUTPUT/check_kernel_identity.py','Executed 16 deterministic 90-digit branch/determinant/Hadamard checks; saved kernel_identity_checks.json. Numerical diagnostics only.','own_output')
if not all(r['finite_check_pass'] for r in rows):
    raise SystemExit('Diagnostic failed')
