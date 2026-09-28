#!/usr/bin/env python3
"""Finite high-precision diagnostics. No interval certification or tail proof."""
import json
import mpmath as mp
mp.mp.dps=65
p,a,b=11,1,2
c=(mp.cos(2*mp.pi*a/p)+mp.cos(2*mp.pi*b/p))/2
th=mp.acos(c); thB=mp.acos(2*c-1); ss=mp.exp(1j*th)
eps=mp.mpf('1e-6'); lam=mp.mpf('1e-7'); tau=mp.mpf('0.005')
de=mp.mpf('0.04'); db=mp.mpf('0.04'); c0=mp.sin(th)/64
sc=(1+eps)*ss

def step(t):
    if t<=0: return mp.mpf(0)
    if t>=1: return mp.mpf(1)
    return mp.exp(-1/t)/(mp.exp(-1/t)+mp.exp(-1/(1-t)))
def plateau(t,l0,l1,r1,r0):
    return step((t-l0)/(l1-l0))*step((r0-t)/(r0-r1))
def pp(t): return plateau(t,de/4,de/2,mp.pi-de/2,mp.pi-de/4)
def mm(t):
    u=t+thB
    return plateau(u,-6*db,-4*db,4*db,6*db)
def geometry(theta):
    n=len(theta); P=sum(pp(t) for t in theta)
    h=[-2*tau*pp(t)+tau*P/(2*n)*mm(t) for t in theta]
    v=[-c0*eps+lam*hi for hi in h]
    y=[mp.exp(vi+1j*t) for vi,t in zip(v,theta)]
    return P,h,y

def phase(s,theta):
    _,_,y=geometry(theta)
    return sum(mp.acos(s+1/s-(yi+1/yi)/2) for yi in y)
def logY(theta):
    _,h,_=geometry(theta)
    return -len(theta)*c0*eps+1j*sum(theta)+lam*sum(h)
def partial(fn,theta,i):
    def one(t):
        q=list(theta);q[i]=t;return fn(q)
    return mp.diff(one,theta[i])
def fmt(z): return mp.nstr(z,32)

def one_case(n):
    theta=[-thB+mp.mpf('0.20'),mp.mpf('0.015'),mp.mpf('0.060')]
    theta += [mp.mpf('-0.8')+mp.mpf('0.7')*i/(n-3) for i in range(n-3)]
    q,r=0,1
    g=[partial(logY,theta,i) for i in (q,r)]
    B=[partial(lambda v:phase(sc,v),theta,i) for i in (q,r)]
    Ds=mp.diff(lambda s:phase(s,theta),sc)
    den=B[0]*g[1]-B[1]*g[0]
    V=[Ds*g[1]/den,-Ds*g[0]/den]
    residualY=g[0]*V[0]+g[1]*V[1]
    residualZ=B[0]*V[0]+B[1]*V[1]-Ds
    # An intentionally incomplete extension: freeze only sum(theta), not logY.
    naive=[Ds/(B[0]-B[1]),-Ds/(B[0]-B[1])]
    naiveY=g[0]*naive[0]+g[1]*naive[1]
    VP=sum(partial(lambda v:geometry(v)[0],theta,i)*vv for i,vv in zip((q,r),V))
    rec={'N':n,'chosen_pair':[q,r],'named_current_index':2,
         'P':fmt(geometry(theta)[0]),'logY_freezing_residual_abs':fmt(abs(residualY)),
         'F_freezing_residual_abs':fmt(abs(residualZ)),
         'correct_field_sum_V':fmt(sum(V)), 'correct_field_VP':fmt(VP),
         'naive_sum_theta_field_logY_residual_abs':fmt(abs(naiveY)),
         'denominator_abs':fmt(abs(den)),
         'theta':[fmt(t) for t in theta]}
    assert abs(residualY)<mp.mpf('1e-50') and abs(residualZ)<mp.mpf('1e-50')
    assert abs(naiveY)>mp.mpf('1e-14')
    if n==6:
        Hess=mp.matrix(n)
        for i in range(n):
            for j in range(n):
                Hess[i,j]=mp.re(partial(lambda v:partial(lambda w:phase(sc,w),v,i),theta,j))
        ev=mp.eigsy(Hess,eigvals_only=True)
        rec['real_phase_Hessian_eigenvalues']=[fmt(x) for x in ev]
        rec['Hessian_symmetry_residual_max']=fmt(max(abs(Hess[i,j]-Hess[j,i]) for i in range(n) for j in range(n)))
    return rec

cases=[one_case(6),one_case(24)]
# The lower-branch tip is not globally concave, even on u>=0.
def phi_original(u):
    yy=mp.exp(-c0*eps+1j*(-thB+u))
    return mp.acos(sc+1/sc-(yy+1/yy)/2)
curve=[{'u_over_eps':str(t),'real_second_derivative':fmt(mp.re(mp.diff(phi_original,eps*t,2)))} for t in (0,1,10,100)]
xi=mp.exp(-1j*thB)
def hh(v,w):return (v-w)/(1-v*w)
zminus=(2*c+1)-mp.sqrt((2*c+1)**2-1)
edge={'branch_with_y_plus_1':fmt(hh(1,xi)*hh(xi,1)),
      'branch_with_y_minus_1':fmt(hh(1,zminus)*hh(xi,-1))}
report={'classification':'finite mpmath floating-point diagnostics; no rigorous rounding, no all-N/epsilon/domain certification',
        'precision_decimal_digits':mp.mp.dps,'point':{'p':p,'a':a,'b':b,'N0':22,'k':241},
        'parameters':{'epsilon':fmt(eps),'lambda':fmt(lam),'tau':fmt(tau),'delta_e':fmt(de),'delta_B':fmt(db),'c0':fmt(c0)},
        'parameter_scope_note':'Diagnostic constants are not asserted to realize the final asymptotic epsilon0. N=6 is an algebraic toy dimension; N=24 is the first tail dimension. No finite test substitutes for P03-P07.',
        'coupled_cases':cases,'branch_curvature_sign_checks':curve,'ungrouped_strict_pair_negative_control':edge}
print(json.dumps(report,indent=2,ensure_ascii=False))
