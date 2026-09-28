"""Exact finite checks of the prime-root Nickel-index lemmas.
Uses integer polynomial reduction modulo cyclotomic polynomials. The finite
checks supplement, but do not replace, the all-prime proof in RESULT.md.
"""
from pathlib import Path
from math import lcm
import json
import sympy as sp
from log_action import log
ROOT=Path(__file__).resolve().parents[1]
t=sp.Symbol('t')

def powers_mod_cyclotomic(L):
    poly=sp.Poly(sp.cyclotomic_poly(L,t),t)
    d=poly.degree(); coeff=[int(poly.nth(i)) for i in range(d)]
    powers=[]; v=[1]+[0]*(d-1)
    for _ in range(L):
        powers.append(tuple(v)); high=v[-1]
        v=[0]+v[:-1]
        if high:
            v=[a-high*c for a,c in zip(v,coeff)]
    assert v==[1]+[0]*(d-1)
    return powers

def add(a,b): return tuple(x+y for x,y in zip(a,b))

def checks(p):
    found=[]; comparisons=0
    for n in range(2,2*p+1,2):
        L=lcm(p,n); powers=powers_mod_cyclotomic(L)
        roots=[add(powers[(j*(L//n))%L],powers[(-j*(L//n))%L]) for j in range(n//2+1)]
        sums={}
        for j in range(len(roots)):
            for k in range(j,len(roots)):
                sums.setdefault(add(roots[j],roots[k]),[]).append([j,k]); comparisons+=1
        for a in range(1,(p-1)//2+1):
            u=add(powers[(a*(L//p))%L],powers[(-a*(L//p))%L])
            target=tuple(2*x for x in u)
            matches=sums.get(target,[])
            if matches: found.append({'n':n,'a':a,'cosine_index_pairs':matches})
            if n<2*p: assert not matches,(p,n,a,matches)
            else: assert matches==[[2*a,2*a]],(p,n,a,matches)
    return {'prime':p,'tested_even_n_max':2*p,'exact_pair_comparisons':comparisons,'matches':found}

rows=[checks(p) for p in [5,7,11,13,17,19]]
out={'arithmetic':'exact integer polynomial remainders; no floating-point root comparisons','sympy_version':sp.__version__,'claims_checked':'minimum even candidate index 2p, unique cosine pair at index 2p, for listed finite primes only','results':rows}
(ROOT/'calculations'/'cyclotomic_checks.json').write_text(json.dumps(out,indent=2)+'\n')
log('compute','RUN_OUTPUT/code/check_cyclotomic.py',{'saved':'calculations/cyclotomic_checks.json','primes':[r['prime'] for r in rows],'arithmetic':'exact integer','sympy_version':sp.__version__})
print(json.dumps(out,indent=2))
