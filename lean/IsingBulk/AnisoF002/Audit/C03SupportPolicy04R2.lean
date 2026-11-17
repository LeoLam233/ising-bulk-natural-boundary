import IsingBulk.AnisoF002.Audit.C03SupportAllowlist
import IsingBulk.AnisoF002.Audit.C03SupportPhysicalAllowlist
import IsingBulk.AnisoF002.Audit.C03SupportGenericIntegrationAllowlist
import IsingBulk.AnisoF002.Audit.C03SupportGeneratedEquationsAllowlist
import IsingBulk.AnisoF002.Audit.C03SupportGibbsAllowlist
import IsingBulk.AnisoF002.Audit.C03SupportFourierAllowlist
import IsingBulk.AnisoF002.Audit.C03SupportTerminalAllowlist
import IsingBulk.AnisoF002.Audit.C03SupportNormalizedEquationsAllowlist
import IsingBulk.AnisoF002.Audit.C03SupportDensityEquationsAllowlist

/-!
Fourth additive cohort policy revision two. The structural/type/value/body
checker remains unchanged. Three literal density/angle equation declarations
have inspected Eq.refl stored proofs; twelve other historical dependencies
match prior exact fingerprints. Only these three owner/type/value entries
are added to revision one. Failed 04_01 and 04_02 and their sources remain.
-/

namespace AnisoF002Audit.C03Cohort04R2
open Lean Elab Command AnisoF002Audit.C03

def cohort04R2HistoricalRules : Array HistoricalRule :=
  historicalRules ++ AnisoF002Audit.C03Physical.literalPhysicalRules ++
    AnisoF002Audit.C03GenericIntegrationRules.genericIntegrationRules ++
    AnisoF002Audit.C03GeneratedEquations.generatedEquationRules ++
    AnisoF002Audit.C03GibbsRules.gibbsRules ++
    AnisoF002Audit.C03FourierRules.fourierContractRules ++
    AnisoF002Audit.C03TerminalRules.terminalInterfaceRules ++
    AnisoF002Audit.C03NormalizedEquations.normalizedEquationRules ++
    AnisoF002Audit.C03DensityEquations.densityEquationRules

def declarationKind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def ruleViolations (env : Environment) (name : Name) (info : ConstantInfo) : Array String := Id.run do
  let some rule := cohort04R2HistoricalRules.find? (fun r => r.name == name)
    | return #[s!"historical_not_allowed:{name}"]
  let mut errors := #[]
  if ownerModule env name != rule.owner then
    errors := errors.push s!"historical_owner_mismatch:{name}"
  if declarationKind info != rule.kind then
    errors := errors.push s!"historical_kind_mismatch:{name}"
  if info.type.hash != rule.typeHash then
    errors := errors.push s!"historical_type_fingerprint_mismatch:{name}"
  if ((info.value? true).map Expr.hash) != rule.valueHash then
    errors := errors.push s!"historical_value_fingerprint_mismatch:{name}"
  return errors

/-- Full checked type/value/constructor closure under the finite catalogue. -/
def scanIn (session : Session) (seeds : List Name) : CoreM Report := do
  let mut todo := seeds
  let mut report : Report := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if report.support.contains name then continue
    report := { report with support := report.support.insert name }
    let node ← directNode session name
    let info := node.info
    if info.isPartial then
      report := { report with violations := report.violations.push s!"partial:{name}" }
    if info.isUnsafe then
      report := { report with violations := report.violations.push s!"unsafe:{name}" }
    if info.isAxiom then
      report := { report with axioms := report.axioms.insert name }
      unless approvedAxiom name do
        report := { report with violations := report.violations.push s!"axiom:{name}" }
    if isHistorical session.env name then
      report := { report with historical := report.historical.insert name }
      report := { report with violations := report.violations ++
        (ruleViolations session.env name info) }
    todo := node.structural.toList ++ todo
  return report

def auditTheoremIn (session : Session) (name : Name)
    (requiredProofConstants : Array Name := #[]) : CommandElabM Unit := do
  for required in requiredProofConstants do
    unless (session.env.checked.get.find? required).isSome do
      throwError "C03_REQUIRED_CONSTANT_UNDECLARED: {required}"
  let node ← liftCoreM <| directNode session name
  unless node.info.isTheorem do throwError "C03_ROOT_NOT_THEOREM: {name}"
  unless (node.info.value? true).isSome do throwError "C03_MISSING_STORED_PROOF: {name}"
  let full ← liftCoreM <| scanIn session [name]
  unless full.violations.isEmpty do
    throwError "C03_STORED_ROUTE_REJECTED: {name}; {full.violations}"
  let proof ← liftCoreM <| scanIn session node.valueSeeds.toList
  unless proof.violations.isEmpty do
    throwError "C03_VALUE_ROUTE_REJECTED: {name}; {proof.violations}"
  let body ← liftCoreM do
    bodyClosureIn session (← directBodyEdges session name).toList
  for required in requiredProofConstants do
    unless body.contains required do
      throwError "C03_REQUIRED_BODY_SUPPORT_ABSENT: {name}; {required}"
  logInfo m!"C03_CHECKED_THEOREM: {name}"
  logInfo m!"C03_ACTUAL_TYPE: {name}; {node.info.type}"
  logInfo m!"C03_STRUCTURAL_SUPPORT_COUNT: {name}; {full.support.toArray.size}"
  logInfo m!"C03_PROOF_SEEDED_SUPPORT_COUNT: {name}; {proof.support.toArray.size}"
  logInfo m!"C03_VALUE_BODY_ONLY_SUPPORT_COUNT: {name}; {body.toArray.size}"
  logInfo m!"C03_AXIOMS: {name}; {full.axioms.toArray.qsort Name.lt}"
  logInfo m!"C03_HISTORICAL_SUPPORT: {name}; {full.historical.toArray.qsort Name.lt}"
  logInfo m!"C03_STORED_ROUTE_PASS: {name}"

/-- Audit every loaded F002 mathematical declaration, including unused/private
helpers. Audit fixtures are excluded by the unchanged provenance classifier. -/
def auditAllMathematicsIn (session : Session) : CommandElabM Unit := do
  let names := (session.env.constants.toList.filter fun (name, _) =>
    isNewMathematics session.env name).map Prod.fst
  unless !names.isEmpty do throwError "C03_EMPTY_MATHEMATICAL_ENVIRONMENT"
  let report ← liftCoreM <| scanIn session names
  unless report.violations.isEmpty do
    throwError "C03_ALL_DECLARATIONS_REJECTED: {report.violations}"
  for name in names.toArray.qsort Name.lt do
    logInfo m!"C03_CHECKED_DECLARATION: {name}"
  logInfo m!"C03_ALL_DECLARATIONS_COUNT: {names.length}"
  logInfo m!"C03_ALL_DECLARATIONS_AXIOMS: {report.axioms.toArray.qsort Name.lt}"
  logInfo m!"C03_ALL_DECLARATIONS_HISTORICAL: {report.historical.toArray.qsort Name.lt}"
  logInfo m!"C03_ALL_DECLARATIONS_SUPPORT_COUNT: {report.support.toArray.size}"
  logInfo m!"C03_ALL_DECLARATIONS_PASS"

/-- Reject a real prohibited endpoint in an actual stored proof. The precise
endpoint must occur in both the proof-seeded structural and body-only graphs. -/
def assertHistoricalRejectedIn (session : Session) (name historical : Name) : CommandElabM Unit := do
  let node ← liftCoreM <| directNode session name
  unless node.info.isTheorem && (node.info.value? true).isSome do
    throwError "C03_NEGATIVE_CONTROL_NO_STORED_THEOREM: {name}"
  let proof ← liftCoreM <| scanIn session node.valueSeeds.toList
  let body ← liftCoreM do
    bodyClosureIn session (← directBodyEdges session name).toList
  unless proof.support.contains historical && proof.historical.contains historical &&
      body.contains historical do
    throwError "C03_NEGATIVE_CONTROL_DID_NOT_REACH_ENDPOINT: {historical}"
  unless proof.violations.contains s!"historical_not_allowed:{historical}" do
    throwError "C03_NEGATIVE_CONTROL_ENDPOINT_WAS_ADMITTED: {historical}"
  let rejected ← try
    auditTheoremIn session name
    pure false
  catch _ => pure true
  unless rejected do throwError "C03_NEGATIVE_CONTROL_ACCEPTED: {name}"
  logInfo m!"C03_REAL_ENDPOINT_ALIAS_REJECTED: {name}; endpoint={historical}; violations={proof.violations.size}"

/-- A mechanism confined to annotations cannot satisfy a body-dependency gate. -/
def assertTypeOnlyRejectedIn (session : Session) (name mechanism : Name) : CommandElabM Unit := do
  let full ← liftCoreM <| scanIn session [name]
  unless full.violations.isEmpty do throwError "C03_TYPE_ONLY_CONTROL_OTHER_VIOLATIONS"
  let body ← liftCoreM do
    bodyClosureIn session (← directBodyEdges session name).toList
  unless full.support.contains mechanism && !body.contains mechanism do
    throwError "C03_TYPE_ONLY_CONTROL_INVALID: {name}; {mechanism}"
  let rejected ← try
    auditTheoremIn session name #[mechanism]
    pure false
  catch _ => pure true
  unless rejected do throwError "C03_TYPE_ONLY_CONTROL_ACCEPTED: {name}"
  logInfo m!"C03_TYPE_ONLY_MECHANISM_REJECTED: {name}; {mechanism}"

/-- The two compiler-generated domain helpers assert only a natural-number
numeral instance. Their independent source/value closure was also inspected. -/
def checkDomainNumeralHelpersIn (session : Session) : CommandElabM Unit := do
  for name in #[`IsingBulk.Anisotropic.inverseTemperature._proof_1,
      `IsingBulk.Anisotropic.sliceY._proof_1] do
    let node ← liftCoreM <| directNode session name
    unless node.info.isTheorem do throwError "C03_NUMERAL_HELPER_NOT_THEOREM: {name}"
    let expected := mkApp (mkConst "Nat.AtLeastTwo".toName) (mkNatLit 2)
    unless ← liftTermElabM (Meta.isDefEq node.info.type expected) do
      throwError "C03_NUMERAL_HELPER_WRONG_TYPE: {name}; {node.info.type}"
    let report ← liftCoreM <| scanIn session [name]
    unless report.violations.isEmpty && report.historical.toArray == #[name] do
      throwError "C03_NUMERAL_HELPER_UNEXPECTED_ROUTE: {name}"
    logInfo m!"C03_DOMAIN_NUMERAL_HELPER_CHECKED: {name}; Nat.AtLeastTwo 2"

end AnisoF002Audit.C03Cohort04R2
