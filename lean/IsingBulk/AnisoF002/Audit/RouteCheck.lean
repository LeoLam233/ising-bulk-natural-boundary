import Lean
import Lean.Util.CollectAxioms

/-!
# F002 stored-proof route checker

All scans use checked constants, declaration types, stored theorem/definition
values (including opaque values), and inductive constructors. Required
mechanisms use a separate body-only graph excluding binder/forall/let type
annotations. Module provenance catches private historical helpers.

An explicit `Session` binds its cache to one immutable checked environment.
It caches only direct dependency edges, never a transitive support set or an
acceptance verdict. Every traversal still checks every visited declaration's
axiom/partial/unsafe flags and the caller's definition-only historical
allowlist. No cache is global or reused with another environment.
-/
namespace AnisoF002Audit
open Lean Elab Command

structure Report where
  support : NameSet := {}
  axioms : NameSet := {}
  historical : NameSet := {}
  violations : Array String := #[]

def approvedAxiom (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

def ownerModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

def isHistorical (env : Environment) (name : Name) : Bool :=
  let owner := ownerModule env name
  ((`IsingBulk).isPrefixOf name && !(`IsingBulk.AnisoF002).isPrefixOf name) ||
    ((`IsingBulk).isPrefixOf owner && !(`IsingBulk.AnisoF002).isPrefixOf owner)

def isNewMathematics (env : Environment) (name : Name) : Bool :=
  let owner := ownerModule env name
  ((`IsingBulk.AnisoF002).isPrefixOf name || (`IsingBulk.AnisoF002).isPrefixOf owner) &&
    !(`IsingBulk.AnisoF002.Audit).isPrefixOf owner

/-- Retain application, let-value/body, metadata-body and projection-argument
constants; exclude lambda, forall-domain and let-type annotations. -/
def bodyConstants (expr : Expr) : NameSet := Id.run do
  let mut todo : List Expr := [expr]
  let mut seen : NameSet := {}
  let mut visited : ExprSet := {}
  while !todo.isEmpty do
    let expr := todo.head!
    todo := todo.tail!
    if visited.contains expr then continue
    visited := visited.insert expr
    match expr with
    | .const name _ => seen := seen.insert name
    | .app fn arg => todo := fn :: arg :: todo
    | .lam _ _ body _ => todo := body :: todo
    | .forallE _ _ body _ => todo := body :: todo
    | .letE _ _ value body _ => todo := value :: body :: todo
    | .mdata _ body => todo := body :: todo
    | .proj _ _ body => todo := body :: todo
    | _ => pure ()
  return seen

/-- Direct edges only. `info` is the constant from the session's checked env. -/
structure DirectNode where
  info : ConstantInfo
  structural : Array Name
  valueSeeds : Array Name
  bodyEdges? : Option (Array Name) := none

/-- A cache cannot be applied to a different environment: every lookup uses
this stored environment rather than the ambient command environment. -/
structure Session where
  env : Environment
  nodes : IO.Ref (NameMap DirectNode)

def makeSession (env : Environment) : CoreM Session := do
  return { env, nodes := ← IO.mkRef {} }

def newSession : CommandElabM Session := do
  liftCoreM <| makeSession (← getEnv)

def directNode (session : Session) (name : Name) : CoreM DirectNode := do
  if let some node := (← session.nodes.get).find? name then
    return node
  let some info := session.env.checked.get.find? name
    | throwError "F002_ROUTE_MISSING_CHECKED_CONSTANT: {name}"
  let valueDeps : Array Name := match info.value? true with
    | some value => value.getUsedConstants
    | none => #[]
  let mut deps := NameSet.ofArray (info.type.getUsedConstants ++ valueDeps)
  if let .inductInfo value := info then
    for ctor in value.ctors do deps := deps.insert ctor
  let node : DirectNode := {
    info, structural := deps.toArray, valueSeeds := valueDeps }
  session.nodes.modify fun nodes => nodes.insert name node
  return node

def directBodyEdges (session : Session) (name : Name) : CoreM (Array Name) := do
  let node ← directNode session name
  if let some edges := node.bodyEdges? then return edges
  let edges := match node.info.value? true with
    | some value => (bodyConstants value).toArray
    | none => #[]
  session.nodes.modify fun nodes => nodes.insert name { node with bodyEdges? := some edges }
  return edges

def scanIn (session : Session) (seeds : List Name)
    (allowedHistorical : Array Name := #[]) : CoreM Report := do
  for allowed in allowedHistorical do
    let info := (← directNode session allowed).info
    unless info.isDefinition do
      throwError "F002_ALLOWLIST_NOT_DEFINITION: {allowed}"
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
      unless allowedHistorical.contains name do
        report := { report with violations := report.violations.push s!"historical:{name}" }
    todo := node.structural.toList ++ todo
  return report

/-- Body-only transitive walk. No declaration type or inductive constructor
edges are followed in this graph. -/
def bodyClosureIn (session : Session) (seeds : List Name) : CoreM NameSet := do
  let mut todo := seeds
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    todo := (← directBodyEdges session name).toList ++ todo
  return seen

/-- Compatibility entrypoint, with a fresh environment-bound session. -/
def scan (env : Environment) (seeds : List Name)
    (allowedHistorical : Array Name := #[]) : CoreM Report := do
  scanIn (← makeSession env) seeds allowedHistorical

def bodySupport (env : Environment) (expr : Expr) : CoreM NameSet := do
  bodyClosureIn (← makeSession env) (bodyConstants expr).toList

def auditRootIn (session : Session) (name : Name)
    (allowedHistorical : Array Name := #[])
    (requiredProofConstants : Array Name := #[]) : CommandElabM Unit := do
  let node ← liftCoreM <| directNode session name
  let info := node.info
  unless info.isTheorem do throwError "F002_ROUTE_ROOT_NOT_THEOREM: {name}"
  unless (info.value? true).isSome do
    throwError "F002_ROUTE_MISSING_STORED_VALUE: {name}"
  let full ← liftCoreM <| scanIn session [name] allowedHistorical
  let proof ← liftCoreM <| scanIn session node.valueSeeds.toList allowedHistorical
  unless full.violations.isEmpty do
    throwError "F002_ROUTE_REJECTED: {name}; {full.violations}"
  unless proof.violations.isEmpty do
    throwError "F002_VALUE_ROUTE_REJECTED: {name}; {proof.violations}"
  let body ← liftCoreM do
    bodyClosureIn session (← directBodyEdges session name).toList
  for required in requiredProofConstants do
    unless body.contains required do
      throwError "F002_REQUIRED_BODY_SUPPORT_ABSENT: {name}; {required}"
  logInfo m!"F002_CHECKED_THEOREM: {name}"
  logInfo m!"F002_ACTUAL_TYPE: {name}; {info.type}"
  logInfo m!"F002_STRUCTURAL_SUPPORT_COUNT: {name}; {full.support.toArray.size}"
  logInfo m!"F002_PROOF_SEEDED_SUPPORT_COUNT: {name}; {proof.support.toArray.size}"
  logInfo m!"F002_VALUE_BODY_ONLY_SUPPORT_COUNT: {name}; {body.toArray.size}"
  logInfo m!"F002_AXIOMS: {name}; {full.axioms.toArray.qsort Name.lt}"
  logInfo m!"F002_HISTORICAL_SUPPORT: {name}; {full.historical.toArray.qsort Name.lt}"
  for dependency in (proof.support.toArray.filter fun n => (`IsingBulk).isPrefixOf n).qsort Name.lt do
    logInfo m!"F002_PROJECT_STORED_SUPPORT: {name}; {dependency}; module={ownerModule session.env dependency}"
  for dependency in (body.toArray.filter fun n => (`IsingBulk).isPrefixOf n).qsort Name.lt do
    logInfo m!"F002_BODY_ONLY_PROJECT_SUPPORT: {name}; {dependency}; module={ownerModule session.env dependency}"
  logInfo m!"F002_STORED_ROUTE_PASS: {name}"

def auditRoot (name : Name) (allowedHistorical : Array Name := #[])
    (requiredProofConstants : Array Name := #[]) : CommandElabM Unit := do
  auditRootIn (← newSession) name allowedHistorical requiredProofConstants

/-- A real forbidden proof must be rejected and the supplied historical
constant must occur in its proof-seeded structural graph. -/
def assertHistoricalRejected (name historical : Name) : CommandElabM Unit := do
  let session ← newSession
  let rejected ← try
    auditRootIn session name
    pure false
  catch _ => pure true
  unless rejected do throwError "F002_NEGATIVE_CONTROL_AUDIT_ACCEPTED: {name}"
  let node ← liftCoreM <| directNode session name
  unless (node.info.value? true).isSome do
    throwError "F002_NEGATIVE_CONTROL_NO_VALUE: {name}"
  let proof ← liftCoreM <| scanIn session node.valueSeeds.toList
  unless proof.support.contains historical do
    throwError "F002_NEGATIVE_CONTROL_DID_NOT_REACH_REAL_HISTORICAL_CONSTANT: {historical}"
  unless proof.historical.contains historical do
    throwError "F002_NEGATIVE_CONTROL_POLICY_MISSED: {historical}"
  unless !proof.violations.isEmpty do
    throwError "F002_NEGATIVE_CONTROL_WAS_ACCEPTED: {name}"
  logInfo m!"F002_NEGATIVE_CONTROL_REJECTED_AS_REQUIRED: {name}; historical={historical}; violations={proof.violations.size}"

/-- A mechanism found only in type annotations cannot satisfy the body check. -/
def assertTypeOnlyRejected (name mechanism : Name) : CommandElabM Unit := do
  let session ← newSession
  let node ← liftCoreM <| directNode session name
  unless (node.info.value? true).isSome do
    throwError "F002_TYPE_ONLY_CONTROL_NO_VALUE: {name}"
  let structural ← liftCoreM <| scanIn session [name]
  let body ← liftCoreM do
    bodyClosureIn session (← directBodyEdges session name).toList
  unless structural.support.contains mechanism do
    throwError "F002_TYPE_ONLY_CONTROL_TYPE_DEPENDENCY_MISSING: {mechanism}"
  unless !body.contains mechanism do
    throwError "F002_TYPE_ONLY_CONTROL_HAS_ACTUAL_BODY_DEPENDENCY: {mechanism}"
  let rejected ← try
    auditRootIn session name #[] #[mechanism]
    pure false
  catch _ => pure true
  unless rejected do throwError "F002_TYPE_ONLY_MECHANISM_WAS_ACCEPTED: {name}"
  logInfo m!"F002_TYPE_ONLY_MECHANISM_REJECTED_AS_REQUIRED: {name}; {mechanism}"

/-- Audit all new mathematical declarations, including private/unused helpers. -/
def auditAllNewDeclarationsIn (session : Session)
    (allowedHistorical : Array Name := #[]) : CommandElabM Unit := do
  let env := session.env
  let names := (env.constants.toList.filter fun (name, _) =>
    isNewMathematics env name).map Prod.fst
  unless !names.isEmpty do throwError "F002_AUDIT_EMPTY_MATHEMATICS"
  let report ← liftCoreM <| scanIn session names allowedHistorical
  unless report.violations.isEmpty do
    throwError "F002_ALL_DECLARATIONS_REJECTED: {report.violations}"
  for name in names.toArray.qsort Name.lt do
    let info := (← liftCoreM <| directNode session name).info
    if info.isTheorem then
      let axioms ← liftCoreM <| Lean.collectAxioms name
      logInfo m!"F002_THEOREM_AXIOMS: {name}; {axioms}"
    logInfo m!"F002_CHECKED_DECLARATION: {name}"
  logInfo m!"F002_ALL_DECLARATIONS_COUNT: {names.length}"
  logInfo m!"F002_ALL_DECLARATIONS_AXIOMS: {report.axioms.toArray.qsort Name.lt}"
  logInfo m!"F002_ALL_DECLARATIONS_HISTORICAL: {report.historical.toArray.qsort Name.lt}"
  logInfo m!"F002_ALL_DECLARATIONS_STRUCTURAL_COUNT: {report.support.toArray.size}"
  logInfo m!"F002_ALL_DECLARATIONS_PASS"

def auditAllNewDeclarations (allowedHistorical : Array Name := #[]) : CommandElabM Unit := do
  auditAllNewDeclarationsIn (← newSession) allowedHistorical

def auditSessionStats (session : Session) : CommandElabM Unit := do
  let nodes ← session.nodes.get
  let mut structuralEdges : Nat := 0
  let mut bodyEdges : Nat := 0
  let mut bodyNodes : Nat := 0
  for (_, node) in nodes.toList do
    structuralEdges := structuralEdges + node.structural.size
    if let some edges := node.bodyEdges? then
      bodyEdges := bodyEdges + edges.size
      bodyNodes := bodyNodes + 1
  logInfo m!"F002_SESSION_CACHE_DIRECT_NODES: {nodes.toList.length}; STRUCTURAL_EDGES={structuralEdges}; BODY_NODES={bodyNodes}; BODY_EDGES={bodyEdges}"

end AnisoF002Audit
