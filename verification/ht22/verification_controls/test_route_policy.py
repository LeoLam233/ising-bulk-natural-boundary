#!/usr/bin/env python3
"""Fast policy unit controls. Synthetic graphs are NOT actual proof evidence."""
import copy,json
from route_policy import (validate, CORE_REQUIRED, MAIN_ROOT, MAIN_REQUIRED,
                          AGGREGATE_REQUIRED, PHYSICAL_REQUIRED, validate_production)

def row(n, deps=(), kind='theorem', module='IsingBulk.HT22.ControlSynthetic'):
    return dict(name=n,kind=kind,module=module,unsafe=False,partial=False,
                has_stored_value=kind!='axiom',type_edges=[],value_edges=list(deps),structural_edges=[])
root='AuditSentinel.synthetic'
base=[row(root,CORE_REQUIRED)]+[row(n) for n in sorted(CORE_REQUIRED)]
summary=dict(root=root,reachable=len(base),axioms=[],unsafe_or_partial=[],missing=[])
cases=[]
def check(label,rows,summ,accepted):
    errors=validate(rows,summ,root)
    passed=(not errors)==accepted
    cases.append(dict(case=label,expected_acceptance=accepted,passed=passed,errors=errors))
check('complete new dependency path',base,summary,True)
for missing in sorted(CORE_REQUIRED):
    rows=copy.deepcopy(base)
    rows[0]['value_edges'].remove(missing)
    rows=[r for r in rows if r['name']!=missing]
    summ=dict(summary,reachable=len(rows))
    check('required theorem omitted: '+missing,rows,summ,False)
# Old endpoint present through a theorem VALUE, not merely an import.
rows=copy.deepcopy(base)
old='IsingBulk.HT.Final.interiorFullBulk_unit_circle_no_extension'
rows[0]['value_edges'].append(old)
rows.append(row(old,module='IsingBulk.HT.Final.FullNaturalBoundary'))
check('old endpoint proof-term bypass',rows,dict(summary,reachable=len(rows)),False)
# An old endpoint merely imported, but absent from the reachable graph, must not
# trigger rejection; the base graph already establishes that positive control.
for edge in ('type_edges','value_edges','structural_edges'):
    rows=copy.deepcopy(base); rows[0][edge].append('AuditSentinel.hiddenAxiom')
    rows.append(row('AuditSentinel.hiddenAxiom',kind='axiom'))
    check('hidden axiom via '+edge,rows,dict(summary,reachable=len(rows),axioms=['AuditSentinel.hiddenAxiom']),False)
rows=copy.deepcopy(base); rows[0]['structural_edges'].append('AuditSentinel.missingSupport')
check('unresolved structural support',rows,dict(summary,reachable=len(rows)+1),False)
rows=copy.deepcopy(base);rows[0]['unsafe']=True
check('unsafe root',rows,summary,False)
rows=copy.deepcopy(base);rows[0]['partial']=True
check('partial root',rows,summary,False)
rows=copy.deepcopy(base);rows[0]['has_stored_value']=False
check('hidden uninspected theorem value',rows,summary,False)
for key,value in [('module',None),('kind','invented'),('has_stored_value','true'),('unsafe',None)]:
    rows=copy.deepcopy(base);rows[0][key]=value
    check('invalid node metadata: '+key,rows,summary,False)
rows=copy.deepcopy(base);rows.append(copy.deepcopy(rows[0]))
check('duplicate graph node',rows,summary,False)
rows=copy.deepcopy(base);rows.append(row('unreachable'))
check('extra unreachable node',rows,summary,False)
check('wrong root',base,dict(summary,root='wrong'),False)
check('unresolved scanner support',base,dict(summary,missing=['absent']),False)
check('summary axiom disagreement',base,dict(summary,axioms=['propext']),False)
types=[dict(name=r['name'],module=r['module'],pretty_type='True',elaborated_expr='const True',level_parameters=[])
       for r in base]
summ=dict(summary,local_types=len(types))
def check_types(label,records,summ,accepted):
    errors=validate(base,summ,root,types=records)
    cases.append(dict(case=label,expected_acceptance=accepted,passed=(not errors)==accepted,errors=errors))
check_types('complete expanded types report',types,summ,True)
check_types('missing expanded type',types[1:],dict(summ,local_types=len(types)-1),False)
check_types('duplicate expanded type',types+[types[0]],dict(summ,local_types=len(types)+1),False)
wrong=copy.deepcopy(types);wrong[0]['module']='wrong'
check_types('expanded type module mismatch',wrong,summ,False)
wrong=copy.deepcopy(types);wrong[0]['elaborated_expr']=''
check_types('missing elaborated expression',wrong,summ,False)
check_types('wrong expanded type count',types,dict(summ,local_types=0),False)

def production_case(decorative=False,omit=None):
    aggregate='IsingBulk.HT22.ht22_full_target'
    all_names=MAIN_REQUIRED|AGGREGATE_REQUIRED|PHYSICAL_REQUIRED
    main_deps=set(CORE_REQUIRED) if decorative else set(MAIN_REQUIRED)
    if omit:main_deps.discard(omit)
    rows=[row(aggregate,all_names),row(MAIN_ROOT,main_deps)]+[
        row(name) for name in sorted(all_names-{MAIN_ROOT})]
    records=[dict(name=r['name'],module=r['module'],pretty_type='True',
                  elaborated_expr='const True',level_parameters=[]) for r in rows]
    summary=dict(root=aggregate,reachable=len(rows),axioms=[],unsafe_or_partial=[],missing=[],local_types=len(records))
    return validate_production(rows,summary,records,aggregate)

errors,sub=production_case()
cases.append(dict(case='production main exact subclosure and separate quantitative exports',
                  passed=not errors and sub['accepted'],errors=errors))
errors,sub=production_case(decorative=True)
cases.append(dict(case='aggregate-only decorative mechanisms do not satisfy main closure',
                  passed=bool(errors) and sub is not None and not sub['accepted'],errors=errors))
for required in sorted(MAIN_REQUIRED-CORE_REQUIRED):
    errors,sub=production_case(omit=required)
    cases.append(dict(case='mechanism removed only from main subclosure: '+required,
                      passed=bool(errors) and any(required in message for message in errors),errors=errors))
print(json.dumps(cases,indent=2))
raise SystemExit(0 if all(c['passed'] for c in cases) else 1)
