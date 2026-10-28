#!/usr/bin/env python3
"""Enforce policy on COMPLETE RootWalker outputs, never on import lists.
This does not replace adversarial review of expanded types or proof bodies.
"""
import argparse, json, pathlib, sys
KINDS = {'axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor'}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN_MODULES = {
    'IsingBulk.HT.Final.FullNaturalBoundary',
    'IsingBulk.HT.Final.PublishedPhysicalTheorem',
    'IsingBulk.HT.Final.PositiveFullNoncancellation',
    'IsingBulk.HT.Final.NegativeFullNoncancellation',
    'IsingBulk.HT.First.OddFirstTheorem',
}
FORBIDDEN_NAMES = {
    'IsingBulk.HT.Tail.' + s for s in [
        'full_odd_tail_small_of_onsite_offsite',
        'selected_positive_absolute_upper_full_odd_tail_small',
        'negative_original_family_absolute_upper_full_odd_tail_small',
        'selected_positive_complex_upper_full_odd_tail_small',
        'negative_original_family_complex_upper_full_odd_tail_small',
        'selected_positive_upper_full_odd_tail_epsilon_zero',
        'negative_original_family_upper_full_odd_tail_epsilon_zero',
    ]
}
CORE_REQUIRED = {
    'IsingBulk.HT22.Final.actual_prime_full_limit',
    'IsingBulk.HT22.Finite.actual_prime_first_limit',
    'IsingBulk.HT22.Finite.prime_lower_coefficient_limit',
    'IsingBulk.HT22.FullTail.actual_absolute_tail',
}
# actual_prime_full_limit is a useful separately exported theorem, but the core
# no-extension proof currently invokes the same assembled limit inline through
# prime_obstruction_of_finite_limits rather than this named corollary.
CORE_REQUIRED.remove('IsingBulk.HT22.Final.actual_prime_full_limit')
PHYSICAL_REQUIRED = {
    'IsingBulk.HT22.PhysicalScope.realSpin_absolute_summability',
    'IsingBulk.HT22.PhysicalScope.realBulk_summable_and_eq',
    'IsingBulk.HT22.PhysicalScope.realSusceptibility_eq_physicalGerm',
    'IsingBulk.HT22.PhysicalScope.realBulk_origin_add_offOrigin',
}
MAIN_ROOT = 'IsingBulk.HT22.Final.f001_natural_boundary'
# These are actual consumed declarations identified by the frozen-source
# crosswalk AND source call sites. Their presence in a report is still pending
# the authorized complete graph extraction; imports do not satisfy this gate.
MAIN_MECHANISM_GROUPS = {
    'whole constrained torus deformation': {
        'IsingBulk.HT22.Physical.signedCoefficient_eq_wholeContour',
        'IsingBulk.HT22.Physical.complete_derivative_partition'},
    'actual odd determinant and ordinary marked minors': {
        'IsingBulk.HT22.Algebra.odd_constantBorderFirst_determinant',
        'IsingBulk.HT22.Algebra.borderedMarkedDeterminant_scaled_bound',
        'IsingBulk.HT22.Algebra.borderedMarkedDeterminant_hadamard'},
    'mixed covariance and actual signed coarea': {
        'IsingBulk.HT22.mixedCovariance',
        'IsingBulk.HT22.Geometry.actual_mixed_covariance_lower',
        'IsingBulk.HT22.Geometry.signed_actual_shell_scale_lintegral',
        'IsingBulk.HT22.Geometry.signed_right_extreme_integral'},
    'true scalar transport and puncture': {
        'IsingBulk.HT22.Tail.coordinateJacobian_piola',
        'IsingBulk.HT22.Tail.physical_transport_factorization',
        'IsingBulk.HT22.Tail.transportedDensity_eq_reconstructed',
        'IsingBulk.HT22.Tail.actual_right_integral_identity'},
    'actual near and far envelopes': {
        'IsingBulk.HT22.Tail.actual_near_scalar_quadratic_full',
        'IsingBulk.HT22.Near.actual_near_shell_sum',
        'IsingBulk.HT22.Far.actual_far_scalar_bound',
        'IsingBulk.HT22.Far.actual_far_density_bound',
        'IsingBulk.HT22.Far.actual_far_shell_sum'},
    'consumed angular V jets and equivalent covariance-Cauchy route': {
        'IsingBulk.HT22.actual_angular_field_uniform_frame_budget',
        'IsingBulk.HT22.actual_angular_field_diameter_bound_from_jets',
        'IsingBulk.HT22.actual_mixed_field_scale_jets_uniform_cap',
        'IsingBulk.HT22.actual_sourceResidual_joint_jets_uniform_cap',
        'IsingBulk.HT22.sourceResidual_joint_jets_of_base_inverse_geometry',
        'IsingBulk.HT22.InverseFactorJets.actual_inverse_factor_frame_jets'},
    'continued inverse and literal physical germ bridge': {
        'IsingBulk.HT22.Geometry.global_one_sided_inverse',
        'IsingBulk.HT22.Geometry.continuedRoot_ne_zero',
        'IsingBulk.HT22.Physical.interiorBulk_eqOn_existing',
        'IsingBulk.HT22.Final.boundary_transfer_of_prime_obstructions'},
}
MAIN_REQUIRED = CORE_REQUIRED | set().union(*MAIN_MECHANISM_GROUPS.values())
AGGREGATE_REQUIRED = {
    MAIN_ROOT,
    'IsingBulk.HT22.Final.actual_prime_full_limit',
    'IsingBulk.HT22.Finite.actual_original_prime_first_asymptotic',
    'IsingBulk.HT22.Physical.physicalSusceptibility_eqOn_existing',
    'IsingBulk.HT22.PhysicalScope.real_temperature_coordinate',
    'IsingBulk.HT22.Physical.full_odd_lattice_norm_summable',
    'IsingBulk.HT22.Physical.oddSeries_real_eq_siteFirst',
    # The precise R, reciprocal-R and G table is an exported quantitative
    # obligation. It is NOT claimed to be consumed by the main boundary proof,
    # which instead uses the equivalent protected covariance-Cauchy route.
    'IsingBulk.HT22.SharpCovarianceJets.actual_sharp_covariance_jets',
}

def validate(rows, summary, expected_root=None, require_physical=False, required_extra=(), types=None):
    errors=[]
    if not isinstance(summary,dict) or not isinstance(summary.get('root'),str):
        return ['malformed summary/root']
    if expected_root is not None and summary.get('root') != expected_root:
        errors.append('root identity mismatch')
    root=summary.get('root')
    byname={}
    for row in rows:
        if not isinstance(row,dict):
            errors.append('malformed node'); continue
        n=row.get('name')
        if not isinstance(n,str) or n in byname:
            errors.append('malformed/duplicate node: '+str(n)); continue
        byname[n]=row
        if row.get('kind') not in KINDS or not isinstance(row.get('module'),str):
            errors.append('missing/malformed kind or module: '+n)
        for k in ('type_edges','value_edges','structural_edges'):
            if not isinstance(row.get(k),list) or not all(isinstance(s,str) for s in row[k]):
                errors.append('malformed '+k+' on '+n)
        if not isinstance(row.get('unsafe'),bool) or not isinstance(row.get('partial'),bool):
            errors.append('missing safety metadata: '+n)
        if not isinstance(row.get('has_stored_value'),bool):
            errors.append('malformed stored value metadata: '+n)
        if row.get('kind') in ('theorem','definition','opaque') and not row.get('has_stored_value'):
            errors.append('missing stored value: '+n)
    if errors: return errors
    seen=set(); queue=[root]; missing=[]
    while queue:
        n=queue.pop()
        if n in seen: continue
        seen.add(n)
        if n not in byname:
            missing.append(n); continue
        row=byname[n]
        queue.extend(row['type_edges']+row['value_edges']+row['structural_edges'])
    if missing: errors.append('unreported/unresolved graph edges: '+','.join(map(str,sorted(missing))))
    if seen != set(byname): errors.append('graph is not exactly the reported rooted closure')
    if type(summary.get('reachable')) is not int or summary['reachable'] != len(seen):
        errors.append('reachable count mismatch')
    if summary.get('missing') != []: errors.append('RootWalker missing support: '+str(summary.get('missing')))
    if summary.get('unsafe_or_partial') != []: errors.append('RootWalker unsafe/partial declarations')
    actual_axioms={n for n in seen if n in byname and byname[n]['kind']=='axiom'}
    if set(summary.get('axioms',[])) != actual_axioms: errors.append('axiom summary/graph mismatch')
    if actual_axioms-ALLOWED_AXIOMS: errors.append('unexpected axioms: '+','.join(sorted(actual_axioms-ALLOWED_AXIOMS)))
    forbidden=[]
    for n in seen & set(byname):
        row=byname[n]
        if row['unsafe'] or row['partial']: errors.append('unsafe/partial node: '+n)
        if n in FORBIDDEN_NAMES or row.get('module') in FORBIDDEN_MODULES:
            forbidden.append(n)
        if require_physical and (n.startswith('IsingBulk.HT22.Controls.') or
                row['module'].startswith('IsingBulk.HT22.Controls.')):
            errors.append('production root depends on author control: '+n)
    if forbidden: errors.append('forbidden old proof-route reachables: '+','.join(sorted(forbidden)))
    required=CORE_REQUIRED | set(required_extra)
    if require_physical: required |= PHYSICAL_REQUIRED
    for n in sorted(required-seen): errors.append('missing required new dependency: '+n)
    # Unit tests may deliberately supply only a synthetic graph. The command
    # line always supplies the complete types report emitted by RootWalker.
    if types is not None:
        local={n for n,r in byname.items() if r['module'].startswith('IsingBulk') or
               n.startswith('AuditSentinel') or n==root}
        actual=set()
        for record in types:
            if not isinstance(record,dict) or not isinstance(record.get('name'),str):
                errors.append('malformed type report row'); continue
            n=record['name']
            if n in actual:errors.append('duplicate type report row: '+n)
            actual.add(n)
            if n not in byname or record.get('module')!=byname[n]['module']:
                errors.append('type/graph module mismatch: '+n)
            for key in ('pretty_type','elaborated_expr'):
                if not isinstance(record.get(key),str) or not record[key]:
                    errors.append('missing '+key+': '+n)
            levels=record.get('level_parameters')
            if not isinstance(levels,list) or not all(isinstance(x,str) for x in levels):
                errors.append('malformed level parameters: '+n)
        if actual!=local:errors.append('type report is not exactly the local rooted closure')
        if type(summary.get('local_types')) is not int or summary['local_types']!=len(types):
            errors.append('local_types count mismatch')
    return errors

def main_subclosure(rows,types,root=MAIN_ROOT):
    """Exact re-rooting of an already structurally validated complete report.

    No union with aggregate-only fields is allowed. Every edge leaving a node
    in this subclosure is traversed, including stored theorem values and all
    inductive/recursor support edges. This is not a source/import approximation.
    """
    byname={row['name']:row for row in rows};seen=set();queue=[root]
    while queue:
        name=queue.pop()
        if name in seen:continue
        seen.add(name)
        if name not in byname:continue
        row=byname[name]
        queue.extend(row['type_edges']+row['value_edges']+row['structural_edges'])
    subset=[row for row in rows if row['name'] in seen]
    local=[row for row in types if row['name'] in seen]
    summary=dict(root=root,reachable=len(seen),
        axioms=[r['name'] for r in subset if r['kind']=='axiom'],
        unsafe_or_partial=[r['name'] for r in subset if r['unsafe'] or r['partial']],
        missing=sorted(seen-set(byname)),local_types=len(local))
    errors=validate(subset,summary,root,required_extra=MAIN_REQUIRED,types=local)
    return dict(root=root,accepted=not errors,reachable=len(seen),local_types=len(local),
                required_dependencies=sorted(MAIN_REQUIRED),errors=errors,
                method='Exact separate rooted subclosure of the complete aggregate proof-term/support graph')

def validate_production(rows,summary,types,expected_root,required_extra=()):
    errors=validate(rows,summary,expected_root,True,AGGREGATE_REQUIRED|set(required_extra),types=types)
    if errors:return errors,None
    sub=main_subclosure(rows,types)
    errors+=['main subclosure: '+message for message in sub['errors']]
    return errors,sub

def main():
    p=argparse.ArgumentParser()
    p.add_argument('base',type=pathlib.Path)
    p.add_argument('--root',required=True)
    p.add_argument('--physical',action='store_true')
    p.add_argument('--require',action='append',default=[])
    a=p.parse_args()
    try:
        rows=[json.loads(s) for s in pathlib.Path(str(a.base)+'.graph.jsonl').read_text().splitlines() if s.strip()]
        summary=json.loads(pathlib.Path(str(a.base)+'.summary.json').read_text())
        types=[json.loads(s) for s in pathlib.Path(str(a.base)+'.types.jsonl').read_text().splitlines() if s.strip()]
        sub=None
        if a.physical:errors,sub=validate_production(rows,summary,types,a.root,a.require)
        else:errors=validate(rows,summary,a.root,False,a.require,types=types)
    except (OSError,ValueError,KeyError,TypeError) as e:
        errors=['invalid/inaccessible report: '+str(e)];sub=None
    print(json.dumps({'accepted':not errors,'errors':errors,'main_route':sub},indent=2))
    return 0 if not errors else 1
if __name__=='__main__': sys.exit(main())
