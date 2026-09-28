"""Exact integer-arithmetic diagnostics for a proved cyclotomic candidate lemma.
For prime q, Phi_q=1+x+...+x^(q-1). A degree <=q-1 coefficient vector
vanishes at a primitive qth root iff all its entries are equal.
The universal argument is in RESULT.md; this finite check is not a density proof.
"""
from pathlib import Path
import json
import math
from log_action import log

def is_prime(q):
    return q>=2 and all(q%d for d in range(2,math.isqrt(q)+1))

def twice_cos_vector(q,j):
    ans=[0]*q
    a=((q+1)//2*j)%q
    sign=-1 if j%2 else 1
    ans[a]+=sign
    ans[(-a)%q]+=sign
    return ans

def main():
    log('computation_start','RUN_OUTPUT/code/exact_geometry.py','Exact cyclotomic reduction; deterministic integer arithmetic.')
    data=[]
    for q in (7,11,13,17,19,23,29,31):
        assert is_prime(q)
        vec=[twice_cos_vector(q,j) for j in range(q+1)]
        targets=[]
        for ell in range(1,(q-1)//2+1):
            matches=[]
            target=[0]*q
            target[ell]+=2
            target[(-ell)%q]+=2
            for j in range(q+1):
                for k in range(j,q+1):
                    v=[vec[j][a]+vec[k][a]-target[a] for a in range(q)]
                    if all(a==v[0] for a in v):
                        matches.append([j,k])
            assert matches==[[2*ell,2*ell]],(q,ell,matches)
            targets.append({'ell':ell,'solutions_in_0_le_j_le_k_le_q':matches})
        # CRT automorphisms for lower even orders: fix n-th roots, send xi_q to xi_q^2.
        automorphisms=[]
        for n in range(2,2*q,2):
            assert math.gcd(n,q)==1
            r=next(r for r in range(1,n*q) if r%n==1 and r%q==2)
            assert math.gcd(r,n*q)==1
            automorphisms.append({'n':n,'automorphism_exponent_mod_nq':r})
        data.append({'prime_q':q,'first_possible_even_particle_order':2*q,'target_count':len(targets),'unique_pair_checks':targets,'lower_order_CRT_checks':automorphisms})
    result={'classification':'Exact finite checks of algebraic lemmas, not a proof that any Ising boundary candidate is an actual singularity.',
            'status':'all_assertions_passed','prime_cases':data,'number_of_target_checks':sum(x['target_count'] for x in data)}
    out=Path(__file__).resolve().parents[1]/'evidence'/'exact_geometry.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'primes':[x['prime_q'] for x in data],'number_of_target_checks':result['number_of_target_checks']},indent=2))
    log('computation_complete','RUN_OUTPUT/code/exact_geometry.py',{'output':'RUN_OUTPUT/evidence/exact_geometry.json','target_checks':result['number_of_target_checks'],'status':'all exact assertions passed'})
if __name__=='__main__':
    main()
