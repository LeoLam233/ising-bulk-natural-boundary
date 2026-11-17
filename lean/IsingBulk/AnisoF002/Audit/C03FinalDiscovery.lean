import IsingBulk.AnisoF002.Audit.RouteCheck
import IsingBulk.AnisoF002.Audit.C03FinalMathRoot

/-! Discovery-only exact type/value audit of generic finite-dimensional algebra and integration. No support rule is amended by this probe. -/

namespace AnisoF002Audit.C03FinalDiscovery
open Lean Elab Command

def kind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def jsonNames (names : Array Name) : Json :=
  toJson ((names.qsort Name.lt).map Name.toString)

structure Walk where
  support : NameSet := {}
  axioms : NameSet := {}
  historical : NameSet := {}
  violations : Array String := #[]

/-- Independent structural traversal: every checked type and stored value,
including opaque values, plus constructors of every encountered inductive. -/
def walk (env : Environment) (seeds : Array Name) : CoreM Walk := do
  let mut todo := seeds.toList
  let mut out : Walk := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if out.support.contains name then continue
    let some info := env.checked.get.find? name
      | throwError "C03_SUPPORT_MISSING_CHECKED_CONSTANT: {name}"
    out := { out with support := out.support.insert name }
    if info.isUnsafe then
      out := { out with violations := out.violations.push s!"unsafe:{name}" }
    if info.isPartial then
      out := { out with violations := out.violations.push s!"partial:{name}" }
    if info.isAxiom then
      out := { out with axioms := out.axioms.insert name }
      unless approvedAxiom name do
        out := { out with violations := out.violations.push s!"axiom:{name}" }
    if isHistorical env name then
      out := { out with historical := out.historical.insert name }
    let mut edges := info.type.getUsedConstants
    if let some value := info.value? true then
      edges := edges ++ value.getUsedConstants
    if let .inductInfo info := info then edges := edges ++ info.ctors.toArray
    todo := edges.toList ++ todo
  return out

def checkedInfo (env : Environment) (name : Name) : CommandElabM ConstantInfo := do
  let some info := env.checked.get.find? name
    | throwError "C03_SUPPORT_MISSING_TYPE: {name}"
  return info

def fullType (info : ConstantInfo) : CommandElabM String :=
  liftTermElabM do
    withOptions (fun opts => opts.setBool `pp.all true) do
      return (← Meta.ppExpr info.type).pretty 180

def fullValue (info : ConstantInfo) : CommandElabM Json := do
  if let some value := info.value? true then
    let text ← liftTermElabM do
      withOptions (fun opts => opts.setBool `pp.all true) do
        return (← Meta.ppExpr value).pretty 180
    return toJson text
  return Json.null

def nodeJson (env : Environment) (name : Name) : CommandElabM Json := do
  let info ← checkedInfo env name
  let valueEdges := (info.value? true).map Expr.getUsedConstants |>.getD #[]
  let ctorEdges := match info with
    | .inductInfo i => i.ctors.toArray
    | _ => #[]
  return Json.mkObj [
    ("name", toJson name.toString),
    ("owner_module", toJson (ownerModule env name).toString),
    ("kind", toJson (kind info)),
    ("historical", toJson (isHistorical env name)),
    ("unsafe", toJson info.isUnsafe),
    ("partial", toJson info.isPartial),
    ("type_edges", jsonNames info.type.getUsedConstants),
    ("stored_value_edges", jsonNames valueEdges),
    ("inductive_constructor_edges", jsonNames ctorEdges)]

def detailJson (env : Environment) (name : Name) : CommandElabM Json := do
  let info ← checkedInfo env name
  let typed ← fullType info
  let defValue ← if info.isDefinition then fullValue info else pure Json.null
  return Json.mkObj [
    ("name", toJson name.toString),
    ("owner_module", toJson (ownerModule env name).toString),
    ("kind", toJson (kind info)),
    ("fully_elaborated_type", toJson typed),
    ("definition_value", defValue),
    ("has_stored_value", toJson (info.value? true).isSome)]


def cohortCandidates (env : Environment) : Array Name :=
  ((env.constants.toList.filter fun (name, _) => isNewMathematics env name).map Prod.fst).toArray

def terminalInterfaceDetail (env : Environment) (name : Name) : CommandElabM Json := do
  let info ← checkedInfo env name
  return Json.mkObj [
    ("name", toJson name.toString),
    ("owner_module", toJson (ownerModule env name).toString),
    ("kind", toJson (kind info)),
    ("unsafe", toJson info.isUnsafe),
    ("partial", toJson info.isPartial),
    ("fully_elaborated_type", toJson (← fullType info)),
    ("stored_value", ← fullValue info),
    ("type_expr_hash", toJson (toString info.type.hash)),
    ("stored_value_expr_hash", match info.value? true with
      | none => Json.null
      | some e => toJson (toString e.hash))]

run_cmd do
  let env ← getEnv
  let terminalInterfaceCandidates := cohortCandidates env
  let full ← liftCoreM <| walk env terminalInterfaceCandidates
  let mut bodySeeds : Array Name := #[]
  for name in terminalInterfaceCandidates do
    let info ← checkedInfo env name
    if let some value := info.value? true then
      bodySeeds := bodySeeds ++ value.getUsedConstants
  let body ← liftCoreM <| walk env bodySeeds
  let historical := full.historical.toArray.qsort Name.lt
  let mechanismRoots : Array Name := #[`IsingBulk.AnisoF002.full_uniform_field_conclusion, `IsingBulk.AnisoF002.full_analytic_conclusion, `IsingBulk.AnisoF002.literal_fullAnalyticConclusion, `IsingBulk.AnisoF002.Isotropic.isotropic_high_normalized_naturalBoundary, `IsingBulk.AnisoF002.Isotropic.isotropic_low_normalized_naturalBoundary, `IsingBulk.AnisoF002.Isotropic.isotropic_positive_prime_no_radial_germ, `IsingBulk.AnisoF002.Isotropic.isotropic_even_prime_no_radial_germ, `IsingBulk.AnisoF002.Isotropic.isotropic_negative_prime_no_radial_germ, `IsingBulk.AnisoF002.Isotropic.exists_actual_full_particle_summable_jet_majorants, `IsingBulk.AnisoF002.Isotropic.actual_full_first_particle_scaled_limit, `IsingBulk.AnisoF002.Isotropic.actual_complete_series_no_radial_germ_of_first, `IsingBulk.AnisoF002.NegativeHT.negative_physical_full_taylor_growth, `IsingBulk.AnisoF002.RegularTail.C03.anisotropic_high_normalized_naturalBoundary, `IsingBulk.AnisoF002.RegularTail.C03.anisotropic_low_normalized_naturalBoundary, `IsingBulk.AnisoF002.RegularTail.C03.literal_realPhysicalIdentification, `IsingBulk.AnisoF002.Physical.literal_realUniformFieldIdentification]
  let report := Json.mkObj [
    ("mechanism_root_details", toJson (← mechanismRoots.mapM (terminalInterfaceDetail env))),
    ("status", toJson "DISCOVERY_ONLY_NOT_REUSE_ADMISSION"),
    ("roots", jsonNames terminalInterfaceCandidates),
    ("violations", toJson full.violations),
    ("structural_closure", jsonNames full.support.toArray),
    ("body_seeded_structural_closure", jsonNames body.support.toArray),
    ("historical", jsonNames historical),
    ("historical_details", toJson (← historical.mapM (terminalInterfaceDetail env))),
    ("axioms", jsonNames full.axioms.toArray),
    ("nodes", toJson (← (full.support.toArray.qsort Name.lt).mapM (nodeJson env)))]
  IO.FS.createDirAll "../evidence/support_c03"
  IO.FS.writeFile "../evidence/support_c03/final_discovery_probe.json" report.pretty
  logInfo m!"C03_FINAL_DISCOVERY_DISCOVERED: roots={terminalInterfaceCandidates.size}; closure={full.support.toArray.size}; historical={historical.size}; axioms={full.axioms.toArray.qsort Name.lt}"
  for name in historical do
    let info ← checkedInfo env name
    logInfo m!"C03_FINAL_DISCOVERY_HISTORICAL: {name}; owner={ownerModule env name}; kind={kind info}; typeHash={info.type.hash}"

end AnisoF002Audit.C03FinalDiscovery
