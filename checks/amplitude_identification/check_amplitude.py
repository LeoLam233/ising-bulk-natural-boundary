"""Exact identities and independent diagnostics for the amplitude conversion.

The general proof is analytic. Finite arithmetic, quadrature, and root samples
corroborate specified steps and do not certify a continuous asymptotic remainder.
"""
import argparse, hashlib, json, pathlib, platform
import mpmath as mp
import sympy as sp

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", required=True)
args = parser.parse_args()
root = pathlib.Path(__file__).resolve().parent
checks = []
def exact(name, value):
    value = sp.simplify(sp.expand(value))
    assert value == 0, (name, value)
    checks.append({'name': name, 'kind': 'exact symbolic identity', 'result': 'zero'})

u, v = sp.symbols('u v', real=True)
exact('H identity', (1-u*u)*v+(1-v*v)*u-(u+v)*(1-u*v))
m = sp.symbols('m', integer=True, positive=True)
exact('even-N one-body/pair phase exponent', m+m*(2*m-1)-2*m*m)
N, sb, T, H, P, G = sp.symbols('N sb T H P G', positive=True)
a = (N*N-1)/2
prefactor = 2/sp.factorial(N) * (2*sp.pi)**(1-N) * 2**(-N*(N-1)) * sb**(-N*N)
angular = (2*sp.pi)**((N-1)/2)*sp.factorial(N)*2**(N*(N-1)/2)*P/(sp.sqrt(N)*2**(a-1)*G)
Q = 2*N*T/sb
d = H/(2*sb**3)
direct_magnitude = sp.pi*prefactor*angular*Q**(a-1)*d**(-a)/2
printed_magnitude = (N*T)**(a-1)*P/(H**a*sp.pi**((N-3)/2)*sp.sqrt(N)*G)
# All bases in this calculation have been declared positive. Complex phases
# are deliberately handled separately; no force=True complex-power identity.
exact('direct radial/Mehta magnitude divided by printed scalar',
      sp.powsimp(sp.expand_power_base(direct_magnitude/printed_magnitude, force=False))-1)
k = sp.symbols('k', integer=True, positive=True)
exact('even-order k parity representation', ((2*m)**2/2-1)-(2*m*m-1))
exact('even-order exponent nu', ((2*m)**2-3)/2-((2*m*m-1)-sp.Rational(1,2)))

# Polynomial division gives a second route to the fractional radial term:
# integral r^(2k)/(q+b*r^2) dr has residual
# (-q)^k b^(-k)/sqrt(q*b) atan(eta*sqrt(b/q)).
r, q, b = sp.symbols('r q b', positive=True)
division = []
for kval in (1, 3, 7, 17):
    regular = sum((-q)**j*r**(2*(kval-j)-2)/b**(j+1) for j in range(kval))
    residual = (-q)**kval/(b**kval*(q+b*r*r))
    exact(f'radial polynomial division k={kval}',
          sp.together(r**(2*kval)/(q+b*r*r)-regular-residual))
    division.append(kval)

# Exact cyclotomic enumeration at a member of the proved prime family.
# zeta_(2p)=-zeta_p^((p+1)/2), so no floating point equality is used.
x = sp.symbols('x')
p = 11
modulus = sp.Poly(sp.cyclotomic_poly(p, x), x, domain=sp.QQ)
def twice_cos(j):
    h = (p+1)//2
    return sp.Poly((-1)**j*(x**((h*j)%p)+x**((-h*j)%p)), x, domain=sp.QQ)
target = twice_cos(2)+twice_cos(4)
pinches = [(j,l) for j in range(2*p) for l in range(1,p)
           if (twice_cos(j)+twice_cos(l)-target).rem(modulus).is_zero]
assert pinches == [(2,4),(4,2),(18,2),(20,4)], pinches

mp.mp.dps = 90
normalizations = []
for sval in (mp.mpf(3)/2, mp.mpf(2), mp.mpf(4)):
    S = sval+1/sval
    def integrand(phi):
        W = S-mp.cos(phi)
        return mp.sin(phi)**2*W/(W*W-1)**mp.mpf('2.5')
    angular_full = mp.quad(integrand, [0, mp.pi/4, mp.pi/2, mp.pi])/(2*mp.pi)
    modulus_k = 1/(sval*sval)
    # Orrick et al. (1.13) uses elliptic modulus k; mpmath uses parameter k^2.
    elliptic = ((1+modulus_k**2)*mp.ellipe(modulus_k**2)
                -(1-modulus_k**2)*mp.ellipk(modulus_k**2)) / (
                   3*mp.pi*(1-modulus_k)*(1-modulus_k**2))
    relative = abs(angular_full/elliptic-1)
    assert relative < mp.mpf('1e-75'), relative
    normalizations.append({'s':str(sval), 'angular_full':mp.nstr(angular_full,70),
                           'elliptic_full':mp.nstr(elliptic,70),
                           'relative_error':mp.nstr(relative,8)})

alpha, beta = 2*mp.pi/11, 4*mp.pi/11
theta = mp.acos((mp.cos(alpha)+mp.cos(beta))/2)
zeta = mp.exp(1j*theta)
NN = 22
kk = NN*NN//2-1
aa = mp.mpf(NN*NN-1)/2
nu = aa-1
HH = mp.sin(alpha)**2*mp.cos(beta)+mp.sin(beta)**2*mp.cos(alpha)
PP = mp.fprod(mp.factorial(j)/2**j for j in range(1,NN))
Rplus = (NN*1j*mp.sin(theta))**nu*PP/(
    HH**aa*mp.pi**(mp.mpf(NN-3)/2)*mp.sqrt(NN)*mp.gamma(aa))
Rminus = (-NN*1j*mp.sin(theta))**nu*PP/(
    HH**aa*mp.pi**(mp.mpf(NN-3)/2)*mp.sqrt(NN)*mp.gamma(aa))
L = (-1)**kk*mp.exp(-1j*kk*theta)*mp.exp(1j*mp.pi*aa/2)*(
    (NN*mp.sin(theta))**nu*PP/(mp.pi**(mp.mpf(NN-2)/2)*mp.sqrt(NN)*HH**aa))
Achart = L*mp.exp(1j*kk*theta)*mp.sqrt(mp.pi)/mp.gamma(aa)
assert abs(Achart/Rminus-1) < mp.mpf('1e-75')
assert abs(Achart/Rplus+1j) < mp.mpf('1e-75')

root_samples = []
for exponent in (4, 8, 12):
    eps = mp.mpf(10)**(-exponent)
    ss = (1+eps)*zeta
    W = ss+1/ss-mp.cos(alpha)
    # Analytic square root normalized at positive real infinity, in Im W>0.
    sq = mp.sqrt(W-1)*mp.sqrt(W+1)
    zz = 1/(W+sq)
    assert abs(zz) < 1 and mp.im(zz) < 0
    root_samples.append({'epsilon':str(eps), 'modulus':mp.nstr(abs(zz),40),
                         'argument':mp.nstr(mp.arg(zz),40),
                         'limiting_argument':mp.nstr(-beta,40)})

result = dict(status='PASS', python=platform.python_version(), sympy=sp.__version__,
              mpmath=mp.__version__, dps=mp.mp.dps, symbolic_checks=checks,
              radial_division_checked_orders=division,
              exact_instance={'p':p,'N':2*p,'a':1,'b':2,'physical_angular_indices':pinches},
              full_observable_quadrature=normalizations, branch_samples=root_samples,
              phase_crosscheck={'Achart_over_Rminus':mp.nstr(Achart/Rminus,60),
                                'Achart_over_Rplus':mp.nstr(Achart/Rplus,60),
                                'complete_full_over_Rminus':mp.nstr(4*Achart/Rminus,60)},
              continuous_asymptotic_certificate=False,
              proof_scope='General analytic derivation is in the accompanying report; finite checks corroborate specified nodes.')
destination = pathlib.Path(args.output)
destination.parent.mkdir(parents=True, exist_ok=True)
if destination.exists():
    raise SystemExit('Refusing to overwrite output receipt: ' + str(destination))
destination.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(result,indent=2))
