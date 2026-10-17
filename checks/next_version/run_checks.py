"""Executed algebra, factorial/amplitude and finite-prime cross-checks.

These analytic arguments were introduced in v0.1-rc5 and are retained in v0.1-rc6. Finite samples do not
certify its continuous-domain estimates or infinite particle sum.
"""
import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path
import random
import sys

import mpmath as mp
import sympy as sp


def pair_identities():
    a,b,c,d=sp.symbols('a b c d',real=True)
    z,w=a+sp.I*b,c+sp.I*d
    ns=lambda q:sp.expand(q*sp.conjugate(q))
    assert sp.expand(ns(1-z*w)-ns(z-w)-(1-ns(z))*(1-ns(w))-4*b*d)==0
    assert sp.expand(ns(z)*ns(1-z*w)-(ns(z)*c-a)**2-(ns(z)*d+b)**2)==0
    Z,W,U=sp.symbols('Z W U')
    kernel=lambda x,y:(x-y)/(1-x*y)
    assert sp.cancel(kernel(Z,W)-kernel(U,W)-(Z-U)*(1-W**2)/((1-Z*W)*(1-U*W)))==0
    rng=random.Random(20261017)
    worst=0.0
    for _ in range(5000):
        z0=rng.uniform(0,1)*mp.exp(-1j*rng.uniform(0,mp.pi))
        w=rng.uniform(0,1)*mp.exp(-1j*rng.uniform(0,mp.pi))
        g=max(1-abs(z0),-z0.imag)
        delta=g*rng.uniform(0,0.5)
        z=z0+delta*mp.exp(1j*rng.uniform(0,2*mp.pi))
        assert abs(1-z0*w)>=g-mp.mpf('1e-65')
        excess=abs(kernel(z,w))-1
        bound=4*abs(z-z0)/g**2
        assert excess<=bound+mp.mpf('1e-60')
        if bound:worst=max(worst,float(max(0,excess)/bound))
    return {'exact_polynomial_identities':3,'larger_half_disk_samples':5000,
            'seed':20261017,'largest_excess_over_bound':worst,
            'sample_scope':'corroboration only; actual source support and disk attachment are Lean theorems'}


def gaussian_moments():
    rows=[]
    for N in (2,4,6,10,22,26):
        # The Gaussian moment is sqrt(2*pi) times this exact integer.
        moment=lambda n:0 if n%2 else sp.factorial2(n-1) if n else sp.Integer(1)
        determinant=sp.det(sp.Matrix(N,N,lambda i,j:moment(i+j)))
        expected=math.prod(math.factorial(j) for j in range(N))
        assert determinant==expected
        rows.append({'N':N,'exact_moment_determinant_equals_product_factorials':True})
    # Independent low-dimensional shape integral, with its coordinate Jacobian.
    # For N=2, tau=(t,-t), Delta(tau)^2=4*t^2.
    q,d=mp.mpf('1.7'),mp.mpf('0.8')
    direct=mp.quad(lambda t:4*t*t/(q-2j*d*t*t)**2,[-mp.inf,0,mp.inf])
    CN=2*mp.sqrt(2)
    reduced=CN/2*q**(-mp.mpf('.5'))*(-1j*d)**(-mp.mpf('1.5'))*mp.beta(mp.mpf('1.5'),mp.mpf('.5'))
    error=abs(direct-reduced)/abs(reduced)
    assert error<mp.mpf('1e-65')
    return {'moment_determinants':rows,'N2_direct_shape_integral_relative_error':str(error)}


def amplitudes():
    rows=[]
    for p,a,b in ((11,1,2),(13,1,3),(17,2,4),(29,3,6)):
        N=2*p;k=N*N//2-1;a0=mp.mpf(N*N-1)/2;nu=a0-1
        alpha,beta=2*mp.pi*a/p,2*mp.pi*b/p
        S=mp.cos(alpha)+mp.cos(beta);theta=mp.acos(S/2)
        d=S*(1-mp.cos(alpha)*mp.cos(beta))/(2*mp.sin(beta)**3)
        Q=2*N*mp.sin(theta)/mp.sin(beta)
        D=Q*mp.exp(-1j*theta)
        K=mp.mpf(2)/mp.factorial(N)*mp.power(2,-N*(N-1))*(2*mp.pi)**(-N)*mp.sin(beta)**(-N*N)
        CN=(2*mp.pi)**(mp.mpf(N-1)/2)*mp.fprod(mp.factorial(j) for j in range(1,N+1))/(mp.sqrt(N)*2**(a0-1)*mp.gamma(a0))
        J=CN/2*Q**(-mp.mpf('.5'))*(-1j*d)**(-a0)*mp.beta(a0,mp.mpf('.5'))
        original=2*mp.pi*K*(-1)**k*mp.factorial(k)*D**k*J
        H=S*(1-mp.cos(alpha)*mp.cos(beta))
        P=mp.fprod(mp.factorial(j)/2**j for j in range(1,N))
        closed=(-1)**k*mp.exp(-1j*k*theta)*mp.exp(1j*mp.pi*a0/2)*(N*mp.sin(theta))**nu*P/(mp.pi**(mp.mpf(N-2)/2)*mp.sqrt(N)*H**a0)
        chart=original*mp.exp(1j*k*theta)*mp.sqrt(mp.pi)/mp.gamma(a0)
        review=lambda t:(N*1j*mp.sin(t))**nu*P/(H**a0*mp.pi**(mp.mpf(N-3)/2)*mp.sqrt(N)*mp.gamma(a0))
        errors=[abs(original/closed-1),abs(chart/review(-theta)-1),abs(chart/review(theta)+1j)]
        assert max(errors)<mp.mpf('1e-65')
        rows.append({'p':p,'a':a,'b':b,'N':N,'max_relative_error':str(max(errors))})
    return {'precision_decimal_digits':mp.mp.dps,'cases':rows,
            'normalization':'single-chart expressions only; source branch/multiplicity identity is not assumed'}


def prime_cover():
    ratios=[]
    for p in list(sp.primerange(11,500)):
        h=2*mp.pi/p;m=(p-1)//4
        ts=[mp.acos((mp.cos(j*h)+mp.cos((j+1)*h))/2) for j in range(1,m)]
        points=sorted(set([t for x in ts for t in (x,mp.pi-x,mp.pi+x,2*mp.pi-x)]))
        gaps=[points[i+1]-points[i] for i in range(len(points)-1)]+[points[0]+2*mp.pi-points[-1]]
        ratio=max(gaps)/(mp.sqrt(10)*h)
        assert ratio<=1
        ratios.append((p,ratio))
    return {'primes_checked':len(ratios),'last_prime':ratios[-1][0],
            'largest_gap_over_proved_bound':str(max(v for _,v in ratios)),
            'scope':'finite diagnostic; general covering proof is analytic in the manuscript'}


def atan_bounds(x,n):
    terms=[(-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n+1)]
    s=sum(terms,F(0));t=(-1)**(n+1)*x**(2*n+3)/F(2*n+3)
    return min(s,s+t),max(s,s+t)


def finite_constant_obstruction():
    # Exact rational intervals from Machin's identity and alternating series.
    a,b=atan_bounds(F(1,5),14);c,d=atan_bounds(F(1,239),4)
    piL,piU=16*a-4*d,16*b-4*c
    assert F(314,100)<piL<piU<F(22,7)
    def cos_bounds(x,n=12):
        s=sum(((-1)**j*x**(2*j)/F(math.factorial(2*j)) for j in range(n+1)),F(0))
        t=(-1)**(n+1)*x**(2*n+2)/F(math.factorial(2*n+2))
        return min(s,s+t),max(s,s+t)
    # cos is decreasing on [0,pi]; use the lower pi endpoint for upper bounds.
    upper_mean=(cos_bounds(2*piL/11)[1]+cos_bounds(4*piL/11)[1])/2
    lower_cos=cos_bounds(F(4,5))[0]
    assert upper_mean<lower_cos # t_min(11)>4/5: its reflected gap exceeds 8/5.
    upper_k=80*piU*piU/F(8,5)**2
    lower_k=80*piL*piL/F(8,5)**2
    assert 241<lower_k and upper_k<337
    return {'classification':'EXACT_RATIONAL_CERTIFICATE',
            'arc_length':'8/5, centered at the positive real axis',
            'pi_interval':[str(piL),str(piU)],
            'positive_cosine_margin':str(lower_cos-upper_mean),
            'k_11':241,'k_13':337,'proposed_k_upper':str(upper_k),
            'conclusion':'the exact constant 80*pi^2 cannot be a uniform finite covering guarantee from this selected family',
            'limit':'does not refute a stronger regularity theorem by another method'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    mp.mp.dps=80
    result={'python':sys.version,'sympy':sp.__version__,'mpmath':mp.__version__,
            'pair':pair_identities(),'gaussian':gaussian_moments(),
            'amplitudes':amplitudes(),'prime_cover':prime_cover(),
            'finite_constant_obstruction':finite_constant_obstruction(),
            'continuous_or_infinite_tail_certificate':False}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
