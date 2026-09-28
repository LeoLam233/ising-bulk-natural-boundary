"""Reproducible consistency checks for ising_audit_manuscript_v7.

Run: python checks.py --output check_results.json
Dependencies: numpy and mpmath.

These checks are not a proof or a uniform verification of the infinite tail.
The cyclotomic tests are exact integer-vector computations at N=2p only.
The quadrature and amplitude tests use non-certified floating-point arithmetic.
"""
import json, math, itertools, argparse
from pathlib import Path
import numpy as np
import mpmath as mp

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_name('check_results.json'))
args=parser.parse_args()
mp.mp.dps=90
out={'scope': {'mpmath_decimal_precision': 90, 'numerical_tests_are_not_interval_certified': True, 'does_not_test_uniform_infinite_tail': True}}

# Exact arithmetic in Q[zeta_p], with basis 1,zeta,...,zeta^(p-2).
def root_vec(p,k):
    k%=p
    if k==p-1: return (-1,)*(p-1)
    v=[0]*(p-1); v[k]=1
    return tuple(v)
def addv(a,b):return tuple(x+y for x,y in zip(a,b))
def two_cos_2p(p,l):
    h=(p+1)//2; sg=(-1)**l
    v=addv(root_vec(p,h*l),root_vec(p,-h*l))
    return tuple(sg*x for x in v)
primes=[11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101]
nt=0; arithmetic_fail=[]
for p in primes:
    vals=[two_cos_2p(p,l) for l in range(p+1)]
    sums={}
    for l in range(p+1):
        for m in range(l,p+1):sums.setdefault(addv(vals[l],vals[m]),[]).append((l,m))
    for a,b in itertools.combinations(range(1,(p-1)//4+1),2):
        nt+=1
        got=sums[addv(vals[2*a],vals[2*b])]
        if got!=[(2*a,2*b)]:arithmetic_fail.append([p,a,b,got])
out['exact_N0_cosine_pair_uniqueness']={'primes':primes,'selected_points':nt,'failures':arithmetic_fail}

# Independent full-site N=2 angular formula against reduced off-site + on-site.
def iz(W):
    rt=np.sqrt(W*W-1+0j)
    z=W-rt
    return np.where(np.abs(z)<1,z,W+rt)
normal=[]
for s in [1.5,2.0,3.0,2*np.exp(0.65j)]:
    n=512;r=0.8
    th=2*np.pi*np.arange(n)/n
    yy=r*np.exp(1j*th);zz=iz(s+1/s-(yy+1/yy)/2)
    if not np.max(np.abs(zz))<r:
        raise RuntimeError(f'Contour radius is not admissible at s={s}')
    yi,yj=yy[:,None],yy[None,:];zi,zj=zz[:,None],zz[None,:]
    Y=yi*yj;Z=zi*zj
    PP=-(yi-yj)**2*Z/(Y*(1-Z)**2)
    R=2*zz**2/(1-zz**2);rr=R/zz
    T=.5*np.mean(PP*(R*yy)[:,None]*(R*yy)[None,:]*(1/Z+1/Y)/((1-Z)*(1-Y)))
    f=.5*np.mean(PP*rr[:,None]*rr[None,:])
    zs=iz(s+1/s-np.cos(th));sh=(1/zs-zs)/2
    C=.5*np.mean(np.sin(th)**2/sh**4*(1+zs**2)/(1-zs**2))
    normal.append({'s':str(s),'C2':str(C),'f00_plus_2T2':str(f+2*T),'relative_error':float(abs(C-f-2*T)/abs(C))})
out['normalization_N2']=normal

# First-chart analytic coefficient ratio, omitting common positive shape-sphere factor.
def first_coefficient(p,a,b):
    N=2*p;k=N*N//2-1;aa=mp.mpf(N*N-1)/2
    al=2*mp.pi*a/p;be=2*mp.pi*b/p;S=mp.cos(al)+mp.cos(be);theta=mp.acos(S/2)
    K=2/mp.factorial(N)*mp.power(2,-N*(N-1))*mp.power(2*mp.pi,-N)*mp.power(mp.sin(be),-N*N)
    Ds=2*N*mp.exp(-1j*theta)*mp.sin(theta)/mp.sin(be)
    Q=2*N*mp.sin(theta)/mp.sin(be)
    d=S*(1-mp.cos(al)*mp.cos(be))/(2*mp.sin(be)**3)
    J=mp.mpf('.5')*mp.power(Q,-mp.mpf('.5'))*mp.power(-1j*d,-aa)*mp.beta(aa,mp.mpf('.5'))
    return 2*mp.pi*K*(-1)**k*mp.factorial(k)*Ds**k*J
amp=[]
for p,a,b in [(11,1,2),(13,1,3),(17,2,4),(43,9,10),(101,24,25)]:
    L=first_coefficient(p,a,b);LL=first_coefficient(p,b,a)
    amp.append({'point':[p,a,b], 'swapped_relative_error':mp.nstr(abs(LL/L-1),8), 'log_abs_common_factor_removed_L':mp.nstr(mp.log(abs(L)),15)})
out['swapped_first_chart_coefficients']=amp

# Reconstruct K_beta from the exact canceled density at Y=1, small real zero-sum shapes.
p=11;a=1;b=2;N=2*p
al=2*mp.pi*a/p;be=2*mp.pi*b/p;SS=mp.cos(al)+mp.cos(be);st=mp.exp(1j*mp.acos(SS/2))
Kbeta=2/mp.factorial(N)*mp.power(2,-N*(N-1))*mp.power(2*mp.pi,-N)*mp.power(mp.sin(be),-N*N)
shape=[mp.mpf(j)-(N-1)/2 for j in range(N)]
Ktests=[]
for e in [4,8,12]:
    h=mp.power(10,-e);eps=h*h
    s=(1+eps)*st
    ys=[mp.exp(1j*(-al+h*t)) for t in shape]
    ph=[mp.acos(s+1/s-(y+1/y)/2) for y in ys]
    zs=[mp.exp(-1j*x) for x in ph]; Z=mp.fprod(zs)
    val=(1/Z+1)/mp.factorial(N)
    for i in range(N):
        val*=2*zs[i]**2/(1-zs[i]**2)*ys[i]/(2*mp.pi)
        for j in range(i):
            PP=-(ys[i]-ys[j])**2*zs[i]*zs[j]/(ys[i]*ys[j]*(1-zs[i]*zs[j])**2)
            val*=PP/(h*(shape[i]-shape[j]))**2
    Ktests.append({'h':str(h),'relative_error_K':mp.nstr(abs(val/Kbeta-1),10),'phase_K_ratio':mp.nstr(mp.arg(val/Kbeta),10)})
out['first_chart_K_reconstruction']=Ktests

# Stress test complete pair on the limiting lower semicircle: deterministic grid.
pair_tests=[]
for p,a,b in [(11,1,2),(43,9,10),(101,24,25)]:
    S=float(mp.cos(2*mp.pi*a/p)+mp.cos(2*mp.pi*b/p))
    th=np.linspace(-np.pi+1e-6,-1e-6,600)
    eps=1e-10;c0=.01;theta=np.arccos(S/2);s=(1+eps)*np.exp(1j*theta)
    y=np.exp(-c0*eps+1j*th);z=iz(s+1/s-(y+1/y)/2)
    pp=-(y[:,None]-y[None,:])**2*z[:,None]*z[None,:]/(y[:,None]*y[None,:]*(1-z[:,None]*z[None,:])**2)
    pair_tests.append({'point':[p,a,b],'max_abs_pair_on_grid':float(np.max(np.abs(pp)))})
out['lower_semicircle_pair_grids']=pair_tests

args.output.parent.mkdir(parents=True, exist_ok=True)
with args.output.open('w', encoding='utf-8') as f:
    json.dump(out,f,ensure_ascii=False,indent=2)
if arithmetic_fail:
    raise RuntimeError('An exact cyclotomic uniqueness check failed; inspect the output JSON.')
print(json.dumps(out,ensure_ascii=False,indent=2))
