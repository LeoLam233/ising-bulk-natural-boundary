"""Independent full-site angular / reduced-contour quadrature comparison.
Finite floating-point diagnostic, not a bound uniform in particle number.
"""
import json
from pathlib import Path
import numpy as np

def interior_root(W):
    z1 = W-np.sqrt(W*W-1+0j)
    z2 = W+np.sqrt(W*W-1+0j)
    return np.where(np.abs(z1)<np.abs(z2), z1, z2)

def compare(s: float, radius: float, n: int) -> dict:
    theta=2*np.pi*np.arange(n)/n
    S=s+1/s
    gamma=np.arccosh(S-np.cos(theta))
    zstd=np.exp(-gamma)
    sh=np.sinh(gamma)
    # Source (n-1)-angle representation with theta_2=-theta_1 for N=2.
    cstd=.5*np.mean(np.sin(theta)**2/sh**4*(1+zstd**2)/(1-zstd**2))
    # Independent onsite Fredholm angular integral, without lattice product kernels.
    h=np.sin((theta[:,None]-theta[None,:])/2)/np.sinh((gamma[:,None]+gamma[None,:])/2)
    onsite=.5*np.mean(h*h/(sh[:,None]*sh[None,:]))
    # Manuscript reduced offsite contour representation, two independent complex y circles.
    y=radius*np.exp(1j*theta)
    W=S-(y+1/y)/2
    z=interior_root(W)
    R=2*z*z/(1-z*z)
    yi,yj=y[:,None],y[None,:]
    zi,zj=z[:,None],z[None,:]
    Y,Z=yi*yj,zi*zj
    pair=-(yi-yj)**2*Z/(Y*(1-Z)**2)
    kernel=(1/Z+1/Y)/((1-Z)*(1-Y))
    tn=.5*np.mean(Y*R[:,None]*R[None,:]*pair*kernel)
    err=cstd-(onsite+2*tn)
    return {'s':s,'radius':radius,'mesh_per_angle':n,
            'Cstd_N2':float(cstd),'onsite_f00_N2':float(onsite),
            'TN2_real':float(tn.real),'TN2_imag':float(tn.imag),
            'absolute_identity_error':float(abs(err)),
            'relative_identity_error':float(abs(err)/abs(cstd)),
            'max_interior_root_modulus':float(np.max(abs(z)))}

if __name__=='__main__':
    rows=[compare(s,r,n) for s,r in [(1.4,.9),(2.,.8),(3.,.75)] for n in [256,512,1024]]
    out={'status':'FINITE DOUBLE-PRECISION QUADRATURE ONLY; NO RIGOROUS ERROR ENCLOSURE',
         'identity':'Cstd_2 = f00^(2) + 2*T_2','checks':rows}
    p=Path(__file__).with_name('independent_normalization_results.json')
    p.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
