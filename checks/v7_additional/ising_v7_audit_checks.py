"""Finite reproducibility checks for ising_audit_manuscript_v7.

These checks do not certify the uniform estimates or the natural-boundary claim.
Run with Python 3 and mpmath installed. No random sampling or network is used.
"""
from __future__ import annotations
import mpmath as mp

mp.mp.dps = 100

def selected_point(p: int, a: int, b: int):
    alpha, beta = 2*mp.pi*a/p, 2*mp.pi*b/p
    if not (0 < alpha < mp.pi/2 and 0 < beta < mp.pi/2 and a != b):
        raise ValueError('Require distinct nonzero acute grid angles.')
    S0 = mp.cos(alpha)+mp.cos(beta)
    theta = mp.acos(S0/2)
    return alpha, beta, S0, theta, mp.exp(1j*theta)

def amplitude_factor(p: int, a: int, b: int, swapped: bool = False):
    alpha, beta, S0, theta, s0 = selected_point(p,a,b)
    if swapped:
        alpha, beta = beta, alpha
    N = 2*p
    k = N*N//2-1
    a0 = mp.mpf(N*N-1)/2
    d = S0*(1-mp.cos(alpha)*mp.cos(beta))/(2*mp.sin(beta)**3)
    Q = 2*N*mp.sin(theta)/mp.sin(beta)
    Ds = 2*N*mp.exp(-1j*theta)*mp.sin(theta)/mp.sin(beta)
    # All omitted factors are the SAME for both ordered charts.
    return (mp.sin(beta)**(-N*N) * Ds**k * Q**(-mp.mpf('0.5'))
            * mp.power(-1j*d, -a0))

def transport_residuals(eps_string: str):
    _, _, S0, _, s0 = selected_point(11,1,2)
    N = 24
    eps = mp.mpf(eps_string)
    c0 = mp.mpf('0.01')
    s = (1+eps)*s0
    S, Sp = s+1/s, 1-1/s**2
    r = mp.exp(-c0*eps)
    thetaB = mp.acos(S0-1)
    us = [mp.mpf(i-mp.mpf('11.5'))/10000 for i in range(N)]
    ys = [r*mp.exp(1j*(-thetaB+u)) for u in us]
    Ws = [S-(y+1/y)/2 for y in ys]
    phis = [mp.acos(W) for W in Ws]
    Wus = [-1j*(y-1/y)/2 for y in ys]
    bs = [-Wu/mp.sin(phi) for Wu,phi in zip(Wus,phis)]
    aa = [Sp/Wu for Wu in Wus]
    A = mp.fsum(aa)
    p,q = 5,18
    V = list(aa)
    V[p] += A*bs[q]/(bs[p]-bs[q])
    V[q] -= A*bs[p]/(bs[p]-bs[q])
    phase_s = [-Sp/mp.sin(phi) for phi in phis]
    sumV = mp.fsum(V)
    phase_error = mp.fsum(b*v-ds for b,v,ds in zip(bs,V,phase_s))
    scale1 = 1+mp.fsum(abs(v) for v in V)
    scale2 = 1+mp.fsum(abs(ds) for ds in phase_s)
    return abs(sumV)/scale1, abs(phase_error)/scale2

def nickel_grid_check():
    _,_,target,_,_ = selected_point(11,1,2)
    rows=[]
    for n in range(2,23,2):
        cs=[mp.cos(2*mp.pi*l/n) for l in range(n//2+1)]
        pairs=[(abs(cs[l]+cs[m]-target),l,m)
               for l in range(len(cs)) for m in range(l,len(cs))]
        best=min(pairs)
        hits=[(l,m) for err,l,m in pairs if err < mp.mpf('1e-90')]
        rows.append((n,mp.nstr(best[0],12),hits))
    return rows

if __name__ == '__main__':
    print('Finite Nickel grid check, p=11, a=1, b=2 (not a proof for all orders):')
    for row in nickel_grid_check():
        print(row)
    print('\nRelative discrepancy of the two ordered amplitude factors:')
    for p,a,b in [(11,1,2),(13,1,3),(17,2,4),(23,3,5)]:
        ratio=amplitude_factor(p,a,b)/amplitude_factor(p,a,b,True)
        print((p,a,b),mp.nstr(abs(ratio-1),8))
    print('\nNormalized residuals of sum V=0 and sum b_i V_i=sum partial_s phi_i:')
    for eps in ['1e-6','1e-12','1e-24','1e-48']:
        print(eps, *(mp.nstr(x,8) for x in transport_residuals(eps)))
    print('\nMinimum full-collision exponents for p=11:')
    N0=22; k=N0*N0//2-1; N=N0+2
    print({'N0':N0,'k':k,'first_tail_N':N,
           'coarea_L':N*N-2*k-4,'flux_exponent':N*N-2*k-3})

    print('\nEndpoint/opposite-group pairs at the limiting boundary (absolute modulus):')
    _,_,S0,_,_ = selected_point(11,1,2)
    def boundary_z(theta):
        W=S0-mp.cos(theta)
        if W > 1:
            return W-mp.sqrt(W*W-1)
        return mp.exp(-1j*mp.acos(W))
    def boundary_pair(theta1,theta2):
        y1,y2=mp.exp(1j*theta1),mp.exp(1j*theta2)
        z1,z2=boundary_z(theta1),boundary_z(theta2)
        return -(y1-y2)**2*z1*z2/(y1*y2*(1-z1*z2)**2)
    for t1,t2 in [(mp.mpf('0'),mp.mpf('-2')),(-mp.pi,mp.mpf('-0.5')),(mp.mpf('0'),-mp.pi)]:
        print(mp.nstr(t1,8),mp.nstr(t2,8),mp.nstr(abs(boundary_pair(t1,t2)),30))
